package deal.test;

import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.ContainerClaimingSeam;
import deal.semantic.ContainerClaimingSeam.OutcomeKind;
import deal.semantic.ContainerClaimingSeam.RecordedOutcome;
import deal.semantic.ContainerClaimingSeam.SeamResult;
import deal.semantic.LoweringSupport;
import deal.semantic.MigrationPlanner;
import deal.semantic.ModuleRoute;
import deal.semantic.RequirementManifestResult;
import deal.semantic.RoutePlanResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticOracle;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.SharedStdlibSemantics;
import deal.semantic.SharedStdlibSemantics.Outcome;
import deal.semantic.SharedStdlibSemantics.StdlibFailure;
import deal.semantic.Target;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RawOp;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.UnicodeScalars;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * The ISSUE-0497 {@code STDLIB_SEMANTICS} claiming and time-lock battery:
 * the {@code ContainerClaimingSeam} home row
 * {@code STDLIB_CALL → STDLIB_SEMANTICS} under the landed full-evidence
 * derivation, the plan-time manifest arm (a checked module containing a
 * cataloged stdlib call claims {@code STDLIB_SEMANTICS} before lowering),
 * the time lock with every negative proof, and the stdlib-export
 * value-read disposition (no claim, no route rule; E6005 while the gap
 * is open; no within-run and no node-level fallback)
 * ({@code stdlib-operations-and-time-lock} D3/D8/D9, Contracts §Time
 * lock and §Stdlib-export value-read disposition, Verification 4 and 5).
 *
 * <p>Tests:
 * <ol>
 *   <li>Home-row arm + derivation: every produced {@code STDLIB_CALL}
 *       homes to {@code STDLIB_SEMANTICS}; the full-evidence derivation
 *       claims the row exactly when it is active and a {@code
 *       STDLIB_CALL} is produced (the closed catalog row
 *       {@code STDLIB_SEMANTICS → {STDLIB_CALL}} holds by construction);
 *       under the current production activation the row is a recorded
 *       staged hand-off; a claim without evidence is the producer-defect
 *       guard.</li>
 *   <li>Manifest arm: a module whose checked source contains a cataloged
 *       stdlib call claims {@code STDLIB_SEMANTICS} at plan time; a
 *       module without a cataloged call, a stdlib-export value read, and
 *       a user-module member call claim nothing.</li>
 *   <li>R-CAPABILITY negatives: a claimed {@code STDLIB_SEMANTICS}
 *       without a produced {@code STDLIB_CALL} and the empty-evidence
 *       {@code STDLIB_TIME_CONFLICT} claim both fail the landed rule.</li>
 *   <li>Time-lock validator negatives: {@code TIME_NOW_MILLIS} is
 *       rejected in a selector position, in the {@code StdlibFunctionId}
 *       position, and as a capability claim.</li>
 *   <li>Time-lock routing: a {@code std/time.nowMillis} module claims
 *       {@code STDLIB_TIME_CONFLICT} and routes {@code LEGACY} in every
 *       purpose — including a {@code COMMON_SHADOW} shadow request —
 *       and never produces a common unit.</li>
 *   <li>Value-read disposition: a stdlib-export read claims no stdlib
 *       capability and adds no route rule; F4 rules 1/3/4/5 route the
 *       module with the D3 disposition and the common unit fails with
 *       the exact E6005 with no reroute and no fallback.</li>
 *   <li>Rule 4's promotion gate covers stdlib-using modules: with
 *       {@code STDLIB_SEMANTICS} shadowed the module reroutes
 *       {@code LEGACY} silently; with it promoted the module routes
 *       {@code SHARED}.</li>
 *   <li>Combined T4 behavior: lowered {@code JSON_PARSE} and
 *       {@code MATH_ABS_INT} scenarios execute through the shared
 *       algorithm and the T4 projection wiring with the exact canonical
 *       projections, and the same module's manifest claims
 *       {@code STDLIB_SEMANTICS}.</li>
 *   <li>Retained-time regression: {@code std/time.lua}, the
 *       {@code jvm-std-time-nowmillis} legacy authority, the
 *       non-fatal staged-failure registry, and the retained as-value
 *       pins stay unchanged (plus the guarded live retained
 *       {@code std/time} behavior probe).</li>
 * </ol>
 */
public class StdlibClaimingTimeLockTest {

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

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
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

    // =========================================================================
    // Shared fixtures
    // =========================================================================

    /** The fixed common-shadow invocation of the carrier tests. */
    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(SemanticProfile.DEAL_V1_2_INT32,
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation publicPreActivation() {
        return CompilerProfileProvider.resolve(ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
    }

    private static CompilerInvocation publicV12Active(CapabilityRegistry registry) {
        return CompilerProfileProvider.resolve(ReleaseState.V1_2_ACTIVE, registry);
    }

    private static CompilerInvocation legacyRegression() {
        return CompilerProfileProvider.resolveLegacyRegression(
            SemanticProfile.LEGACY_SAFE_INT, ReleaseState.PRE_ACTIVATION,
            CapabilityRegistry.releaseRegistry());
    }

    /**
     * Compiles the fixture sources under one temp source directory
     * through the full orchestrator pipeline (phase 3 + the checked
     * project builder) and returns the checked project result.
     */
    private static CheckedProjectBuildResult compileProject(Path tmp,
            Map<String, String> sources, String entryName) {
        try {
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
            return checked;
        } catch (Exception e) {
            fail(entryName + " fixture setup threw: " + e);
            return null;
        }
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

    /** The module's requirement manifest by module path, or null. */
    private static SemanticRequirementManifest manifestOf(RequirementManifestResult manifests,
                                                          ModuleId moduleId) {
        if (manifests == null || manifests.hasErrors() || manifests.manifests() == null) {
            return null;
        }
        for (SemanticRequirementManifest manifest : manifests.manifests()) {
            if (manifest.moduleId().equals(moduleId)) {
                return manifest;
            }
        }
        return null;
    }

    /** The manifests of the checked project under the given invocation. */
    private static RequirementManifestResult manifestsOf(CheckedProjectBuildResult checked,
                                                         CompilerInvocation invocation) {
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation,
            checked.input(), checked.index());
        check(manifests != null && !manifests.hasErrors(),
            "the manifest computation is clean"
                + (manifests == null ? " (null)" : ": " + manifests.diagnostics()));
        return manifests;
    }

    /** The validated-lowering facts of the checked project (R-PROFILE). */
    private static SemanticIrValidator.ComparisonFacts factsOf(
            CheckedProjectBuildResult checked) {
        return new SemanticIrValidator.ComparisonFacts(
            checked.index().interfaceIndexDigest(), SemanticProfile.DEAL_V1_2_INT32,
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash());
    }

    /**
     * Lowers the named subject module of the checked project through the
     * carrier (manifests → full-program lowerer). The outcome is asserted
     * by the caller.
     */
    private static SemanticLowerer.LoweringResult lowerSubject(
            CheckedProjectBuildResult checked, String modulePath) {
        CheckedModuleInput subject = moduleOf(checked.input(), modulePath);
        if (subject == null) {
            fail("the checked project has no module " + modulePath);
            return null;
        }
        RequirementManifestResult manifests = manifestsOf(checked, invocation());
        if (manifests == null || manifests.hasErrors()) {
            return null;
        }
        SemanticRequirementManifest manifest = manifestOf(manifests, subject.moduleId());
        if (manifest == null) {
            fail("no manifest for module " + modulePath);
            return null;
        }
        List<ModuleId> moduleIds = new ArrayList<>();
        for (CheckedModuleInput module : checked.input().modules()) {
            moduleIds.add(module.moduleId());
        }
        return SemanticLowerer.lowerModuleFullProgram(
            subject, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
            checked.index().interfaceIndexDigest(),
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
            SemanticIdAllocator.over(moduleIds));
    }

    /** Every {@code STDLIB_CALL} op of the unit in source order. */
    private static List<SemanticOp> stdlibOps(LoweredModuleUnit unit) {
        List<SemanticOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL) {
                ops.add(op);
            }
        }
        return ops;
    }

    /** The single {@code STDLIB_CALL} carrying the given id, or null. */
    private static SemanticOp stdlibOpBy(LoweredModuleUnit unit,
                                         StdlibFunctionId function) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL
                    && ((KindPayload.StdlibCallPayload) op.payload()).function() == function) {
                return op;
            }
        }
        return null;
    }

    /**
     * Serializes one raw unit through the text surface and validates it.
     */
    private static Optional<CompilerDiagnostic> validateText(RawUnit raw,
            SemanticIrValidator.ComparisonFacts facts) {
        return SemanticIrValidator.validateText(
            ContractSnapshotCanonicalizer.serializeText(
                ContractSnapshotCanonicalizer.toJson(raw)),
            facts);
    }

    // =========================================================================
    // Raw-op modification helpers (the T2 pattern: the only defect is the
    // targeted field, the digest recomputed where the snapshot changed)
    // =========================================================================

    /** One raw op with a snapshot field replaced and the digest recomputed. */
    private static RawOp withSnapshotField(RawOp op, String key, String value) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.snapshot().entries()) {
            entries.add(entry.key().equals(key)
                ? CanonicalJson.e(key, CanonicalJson.str(value)) : entry);
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(entries);
        String digest = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(snapshot);
        String selector = "selector".equals(key) ? value : op.selector();
        return new RawOp(op.opId(), op.kind(), op.failurePolicy(), op.parentOpId(),
            op.resultValue(), op.resultToken(), op.resultType(), op.operands(),
            op.operandTypes(), op.payload(), selector, digest, snapshot);
    }

    /** One raw op with a payload field replaced (the snapshot stays untouched). */
    private static RawOp withPayloadField(RawOp op, String key, String value) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.payload().entries()) {
            entries.add(entry.key().equals(key)
                ? CanonicalJson.e(key, CanonicalJson.str(value)) : entry);
        }
        CanonicalJson.Obj payload = CanonicalJson.obj(entries);
        return new RawOp(op.opId(), op.kind(), op.failurePolicy(), op.parentOpId(),
            op.resultValue(), op.resultToken(), op.resultType(), op.operands(),
            op.operandTypes(), payload, op.selector(), op.canonicalDigest(), op.snapshot());
    }

    /** One raw op re-kindn to UNARY with the reserved selector (snapshot +
     *  digest recomputed so the selector position is the only defect). */
    private static RawOp asUnaryWithSelector(RawOp op, String selector) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.snapshot().entries()) {
            entries.add(entry.key().equals("selector")
                ? CanonicalJson.e("selector", CanonicalJson.str(selector)) : entry);
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(entries);
        String digest = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(snapshot);
        return new RawOp(op.opId(), "UNARY", op.failurePolicy(), op.parentOpId(),
            op.resultValue(), op.resultToken(), op.resultType(), op.operands(),
            op.operandTypes(), op.payload(), selector, digest, snapshot);
    }

    /** One raw unit with the named capabilities added to its claim set. */
    private static RawUnit withCapabilities(RawUnit raw, String... extra) {
        List<String> capabilities = new ArrayList<>(raw.requiredCapabilities());
        capabilities.addAll(List.of(extra));
        return new RawUnit(raw.modulePath(), raw.semanticProfile(), raw.interfaceHash(),
            raw.loweringContextHash(), capabilities, raw.coverage(), raw.bindings(),
            raw.ops());
    }

    /** Rebuilds one raw unit with a per-op transform. */
    private interface OpTransform {
        RawOp apply(RawOp op);
    }

    private static RawUnit transformOps(RawUnit raw, OpTransform transform) {
        List<RawOp> ops = new ArrayList<>();
        for (RawOp op : raw.ops()) {
            ops.add(transform.apply(op));
        }
        return new RawUnit(raw.modulePath(), raw.semanticProfile(), raw.interfaceHash(),
            raw.loweringContextHash(), raw.requiredCapabilities(), raw.coverage(),
            raw.bindings(), ops);
    }

    // =========================================================================
    // 1. The home-row arm and the full-evidence derivation
    // =========================================================================

    static void testHomeRowsArmAndDerivation() throws Exception {
        System.out.println("-- Home-row arm: STDLIB_CALL → STDLIB_SEMANTICS + derivation --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-home");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"
                    import * as str from "std/string"

                    function run(): null {
                      console.log("hi")
                      let n: int = str.length("abc")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
                "the stdlib module lowers through the validator/chain protocol/"
                    + "control-flow validator: " + (lowering == null ? "null"
                        : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            LoweredModuleUnit unit = lowering.unit();
            List<SemanticOp> calls = stdlibOps(unit);
            check(calls.size() == 2,
                "the fixture produces 2 STDLIB_CALL ops; got " + calls.size());

            // The pinned home row: every produced STDLIB_CALL homes to
            // STDLIB_SEMANTICS — the closed single-family catalog row.
            for (SemanticOp call : calls) {
                check(ContainerClaimingSeam.homeRows(call)
                        .equals(List.of(deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS)),
                    "homeRows(STDLIB_CALL) = [STDLIB_SEMANTICS] ("
                        + ((KindPayload.StdlibCallPayload) call.payload()).function() + ")");
            }
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.STDLIB_CALL) {
                    check(!ContainerClaimingSeam.homeRows(op)
                            .contains(deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                        "no non-stdlib op homes to STDLIB_SEMANTICS (" + op.kind() + ")");
                }
            }

            // The op-evidence derivation: a produced STDLIB_CALL fully
            // evidences STDLIB_SEMANTICS → {STDLIB_CALL} by construction.
            check(ContainerClaimingSeam.fullyEvidenced(unit.ops(),
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                "the produced STDLIB_CALL ops fully evidence STDLIB_SEMANTICS → "
                    + "{STDLIB_CALL}");

            // Staged state: under the current production activation
            // (E6_GATE_ACTIVATION) the row is inactive — the derivation
            // excludes it and every STDLIB_CALL position records the
            // staged hand-off (the gate flip is the epic tail's).
            Set<deal.semantic.ir.SemanticCapability> productionActive =
                ContainerClaimingSeam.E6_GATE_ACTIVATION;
            Set<deal.semantic.ir.SemanticCapability> stagedDerived =
                ContainerClaimingSeam.deriveClaims(unit.ops(), productionActive);
            check(!stagedDerived.contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                "under E6_GATE_ACTIVATION the derivation excludes STDLIB_SEMANTICS "
                    + "(staged until the epic gate hand-off); got " + stagedDerived);
            SeamResult stagedSeam = ContainerClaimingSeam.check(unit.ops(),
                productionActive, stagedDerived, unit.moduleId());
            check(stagedSeam.failure() == null,
                "the staged check records no failure");
            for (RecordedOutcome outcome : stagedSeam.outcomes()) {
                if (outcome.opKind() == SemanticOpKind.STDLIB_CALL) {
                    check(outcome.home()
                            == deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS
                            && outcome.outcome() == OutcomeKind.STAGED_HAND_OFF,
                        "a staged STDLIB_CALL position records STAGED_HAND_OFF for "
                            + "the STDLIB_SEMANTICS home row");
                }
            }

            // Augmented activation: the derivation claims the row and the
            // seam check records CLAIMED — the closed catalog row holds by
            // construction of the derivation.
            Set<deal.semantic.ir.SemanticCapability> augmented =
                EnumSet.copyOf(ContainerClaimingSeam.E6_GATE_ACTIVATION);
            augmented.add(deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS);
            Set<deal.semantic.ir.SemanticCapability> derived =
                ContainerClaimingSeam.deriveClaims(unit.ops(), augmented);
            check(derived.contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                "with the row active the derivation claims STDLIB_SEMANTICS from the "
                    + "produced STDLIB_CALL; got " + derived);
            SeamResult seam = ContainerClaimingSeam.check(unit.ops(), augmented,
                derived, unit.moduleId());
            check(seam.failure() == null,
                "the augmented check passes (the unit carries the derived claim)");
            int claimedPositions = 0;
            for (RecordedOutcome outcome : seam.outcomes()) {
                if (outcome.opKind() == SemanticOpKind.STDLIB_CALL) {
                    check(outcome.outcome() == OutcomeKind.CLAIMED,
                        "an active STDLIB_CALL position records CLAIMED for the "
                            + "STDLIB_SEMANTICS home row");
                    claimedPositions++;
                }
            }
            check(claimedPositions == calls.size(),
                "every produced STDLIB_CALL position records CLAIMED; got "
                    + claimedPositions + " of " + calls.size());

            // The producer-defect guard: a claim without full evidence is
            // impossible by the derivation (the row inactive).
            boolean guarded = false;
            try {
                ContainerClaimingSeam.check(unit.ops(), productionActive, derived,
                    unit.moduleId());
            } catch (IllegalArgumentException expected) {
                guarded = true;
            }
            check(guarded,
                "a claim of the inactive STDLIB_SEMANTICS row is the producer-defect "
                    + "guard (never a silent claim without evidence)");

            // Negative direction: a unit without a STDLIB_CALL never
            // evidences the row. Lower the plain module.
            CheckedProjectBuildResult plainChecked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    function run(): null {
                      let n: int = 1
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (plainChecked == null) {
                return;
            }
            SemanticLowerer.LoweringResult plainLowering = lowerSubject(plainChecked, "lib");
            check(plainLowering != null && !plainLowering.hasErrors()
                    && plainLowering.unit() != null,
                "the plain module lowers cleanly: " + (plainLowering == null ? "null"
                    : plainLowering.diagnostics()));
            if (plainLowering != null && !plainLowering.hasErrors()
                    && plainLowering.unit() != null) {
                check(!ContainerClaimingSeam.fullyEvidenced(plainLowering.unit().ops(),
                        deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                    "a unit without a STDLIB_CALL never evidences STDLIB_SEMANTICS");
                check(!ContainerClaimingSeam.deriveClaims(plainLowering.unit().ops(),
                        augmented).contains(
                            deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                    "the derivation never claims STDLIB_SEMANTICS without a produced "
                        + "STDLIB_CALL");
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 2. The plan-time manifest arm
    // =========================================================================

    static void testManifestArm() throws Exception {
        System.out.println("-- Manifest arm: cataloged stdlib call → STDLIB_SEMANTICS --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-manifest");
        try {
            // (a) A cataloged stdlib call claims STDLIB_SEMANTICS at plan
            // time — under every invocation purpose (the claim derives
            // from the checked source, never the purpose).
            CheckedProjectBuildResult stdlibChecked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"

                    function run(): null {
                      console.log("x")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (stdlibChecked == null) {
                return;
            }
            ModuleId libId = moduleOf(stdlibChecked.input(), "lib").moduleId();
            for (CompilerInvocation purpose : List.of(invocation(),
                    publicPreActivation(), legacyRegression())) {
                RequirementManifestResult manifests =
                    manifestsOf(stdlibChecked, purpose);
                if (manifests == null || manifests.hasErrors()) {
                    continue;
                }
                SemanticRequirementManifest lib = manifestOf(manifests, libId);
                check(lib != null && lib.capabilities().contains(
                        deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                    "the stdlib-calling module claims STDLIB_SEMANTICS at plan time "
                        + "(purpose " + purpose.purpose() + "): "
                        + (lib == null ? "no manifest" : lib.capabilities()));
                check(lib != null && lib.capabilities().contains(
                        deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES),
                    "the same manifest keeps the mandatory FOUNDATION_VALUES claim");
            }

            // (b) A module without a cataloged call never claims it.
            CheckedProjectBuildResult plainChecked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    function run(): null {
                      let n: int = 1
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (plainChecked == null) {
                return;
            }
            {
                RequirementManifestResult manifests =
                    manifestsOf(plainChecked, invocation());
                if (manifests != null && !manifests.hasErrors()) {
                    SemanticRequirementManifest lib = manifestOf(manifests,
                        moduleOf(plainChecked.input(), "lib").moduleId());
                    check(lib != null && !lib.capabilities().contains(
                            deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                        "a module without a cataloged call claims no STDLIB_SEMANTICS: "
                            + (lib == null ? "no manifest" : lib.capabilities()));
                }
            }

            // (c) A stdlib-export value read claims nothing from the read.
            CheckedProjectBuildResult valueRead = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"

                    function run(): null {
                      let g: (x: string) => null = console.log
                      g("x")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (valueRead == null) {
                return;
            }
            {
                RequirementManifestResult manifests =
                    manifestsOf(valueRead, invocation());
                if (manifests != null && !manifests.hasErrors()) {
                    SemanticRequirementManifest lib = manifestOf(manifests,
                        moduleOf(valueRead.input(), "lib").moduleId());
                    check(lib != null
                            && !lib.capabilities().contains(
                                deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS)
                            && !lib.capabilities().contains(
                                deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
                        "the value-read module claims no stdlib capability from the "
                            + "read: " + (lib == null ? "no manifest"
                                : lib.capabilities()));
                }
            }

            // (d) A user-module member call is never recognized, never
            // claimed (the checked-fact predicate, never a name pair).
            CheckedProjectBuildResult userCall = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "util.deal", """
                    export function length(s: string): int {
                      return 0
                    }
                    """,
                "lib.deal", """
                    import * as s from "./util"

                    function run(): null {
                      s.length("x")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (userCall == null) {
                return;
            }
            {
                RequirementManifestResult manifests =
                    manifestsOf(userCall, invocation());
                if (manifests != null && !manifests.hasErrors()) {
                    SemanticRequirementManifest lib = manifestOf(manifests,
                        moduleOf(userCall.input(), "lib").moduleId());
                    check(lib != null && !lib.capabilities().contains(
                            deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                        "a user-module member call claims no STDLIB_SEMANTICS (the "
                            + "import resolves to IMPLEMENTATION, never STDLIB): "
                            + (lib == null ? "no manifest" : lib.capabilities()));
                }
            }

            // (e) The shadowed-binding negative (D1): a nested-scope
            // binding shadowing a stdlib import alias with a catalog-key
            // member call never claims STDLIB_SEMANTICS. The checker
            // resolves the callee identifier at the call site to the
            // local class instance — the int argument is accepted only
            // because the local field type is (x: int) => null, while
            // the std/console export is (string) => null — so the plan-
            // time arm must resolve the same site scope and classify
            // the call as the ordinary CALL form, never a cataloged
            // stdlib call.
            CheckedProjectBuildResult shadowedChecked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"

                    class C {
                      log: (x: int) => null = function(x: int): null {
                        return null
                      }
                    }

                    function run(): null {
                      let console: C = { log: function(x: int): null { return null } }
                      console.log(1)
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (shadowedChecked == null) {
                return;
            }
            {
                RequirementManifestResult manifests =
                    manifestsOf(shadowedChecked, invocation());
                if (manifests != null && !manifests.hasErrors()) {
                    SemanticRequirementManifest lib = manifestOf(manifests,
                        moduleOf(shadowedChecked.input(), "lib").moduleId());
                    check(lib != null && !lib.capabilities().contains(
                            deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                        "a nested-scope binding shadowing a stdlib import alias never "
                            + "claims STDLIB_SEMANTICS (the checker resolved the call "
                            + "site to the local binding, not the import): "
                            + (lib == null ? "no manifest" : lib.capabilities()));
                }
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 3. R-CAPABILITY negatives: a claim without the produced op
    // =========================================================================

    static void testRCapabilityNegatives() throws Exception {
        System.out.println("-- R-CAPABILITY: claimed STDLIB_SEMANTICS without STDLIB_CALL --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-rcap");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    function run(): null {
                      let n: int = 1
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
                "the plain module lowers cleanly: " + (lowering == null ? "null"
                    : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            RawUnit raw = RawUnit.fromTyped(lowering.unit());
            SemanticIrValidator.ComparisonFacts facts = factsOf(checked);

            // Positive control: the untouched unit passes both surfaces.
            Optional<CompilerDiagnostic> untouched =
                SemanticIrValidator.validate(lowering.unit(), facts);
            check(untouched.isEmpty(),
                "the untouched plain unit passes the closed validator"
                    + (untouched.isPresent() ? ": " + untouched.get().message() : ""));

            // The evidence negative: a claimed STDLIB_SEMANTICS without a
            // produced STDLIB_CALL fails R-CAPABILITY — the landed
            // claimed→evidence direction, the row's exact requirement.
            Optional<CompilerDiagnostic> semanticsClaim = validateText(
                withCapabilities(raw, "STDLIB_SEMANTICS"), facts);
            check(semanticsClaim.isPresent(),
                "a STDLIB_SEMANTICS claim without a STDLIB_CALL fails validation");
            if (semanticsClaim.isPresent()) {
                check(semanticsClaim.get().message().contains("R-CAPABILITY")
                        && semanticsClaim.get().message().contains("STDLIB_SEMANTICS")
                        && semanticsClaim.get().message().contains("STDLIB_CALL"),
                    "the failure is R-CAPABILITY naming the missing required "
                        + "operation (STDLIB_CALL): " + semanticsClaim.get().message());
            }

            // The empty-evidence routing marker: STDLIB_TIME_CONFLICT is
            // unsatisfiable by construction (S4 → {}).
            Optional<CompilerDiagnostic> conflictClaim = validateText(
                withCapabilities(raw, "STDLIB_TIME_CONFLICT"), facts);
            check(conflictClaim.isPresent(),
                "a STDLIB_TIME_CONFLICT claim fails validation (the empty evidence "
                    + "set is unsatisfiable)");
            if (conflictClaim.isPresent()) {
                check(conflictClaim.get().message().contains("R-CAPABILITY")
                        && conflictClaim.get().message().contains("STDLIB_TIME_CONFLICT")
                        && conflictClaim.get().message().contains("routing marker"),
                    "the failure is R-CAPABILITY naming the routing marker: "
                        + conflictClaim.get().message());
            }

            // The capability-claim naming the reserved selector: rejected
            // in the closed SemanticCapability position.
            Optional<CompilerDiagnostic> reservedCapability = validateText(
                withCapabilities(raw, "TIME_NOW_MILLIS"), facts);
            check(reservedCapability.isPresent(),
                "a capability claim naming TIME_NOW_MILLIS fails validation");
            if (reservedCapability.isPresent()) {
                check(reservedCapability.get().message().contains("TIME_NOW_MILLIS")
                        && reservedCapability.get().message()
                            .contains("SemanticCapability"),
                    "the failure rejects TIME_NOW_MILLIS in the closed "
                        + "SemanticCapability position: "
                        + reservedCapability.get().message());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 4. Time-lock validator negatives
    // =========================================================================

    static void testTimeLockValidatorNegatives() throws Exception {
        System.out.println("-- Time lock: reserved-name and selector negatives --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-timeneg");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as str from "std/string"

                    function run(): null {
                      let n: int = str.length("abc")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
                "the stdlib module lowers cleanly: " + (lowering == null ? "null"
                    : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            RawUnit raw = RawUnit.fromTyped(lowering.unit());
            SemanticIrValidator.ComparisonFacts facts = factsOf(checked);

            // Positive control: the untouched unit passes.
            Optional<CompilerDiagnostic> untouched = validateText(raw, facts);
            check(untouched.isEmpty(),
                "the untouched stdlib unit passes the text surface"
                    + (untouched.isPresent() ? ": " + untouched.get().message() : ""));

            // (a) TIME_NOW_MILLIS in the STDLIB_CALL selector position
            // (the selector the stdlib row would carry) → R-RESERVED-NAME.
            RawUnit selectorNegative = transformOps(raw, op ->
                op.kind().equals("STDLIB_CALL")
                    ? withSnapshotField(op, "selector", "TIME_NOW_MILLIS") : op);
            Optional<CompilerDiagnostic> selectorFailure =
                validateText(selectorNegative, facts);
            check(selectorFailure.isPresent(),
                "TIME_NOW_MILLIS in the STDLIB_CALL selector position fails validation");
            if (selectorFailure.isPresent()) {
                check(selectorFailure.get().message().contains("R-RESERVED-NAME")
                        && selectorFailure.get().message().contains("TIME_NOW_MILLIS"),
                    "the failure is R-RESERVED-NAME on the reserved selector name: "
                        + selectorFailure.get().message());
            }

            // (b) TIME_NOW_MILLIS in a UnarySelector position: the first
            // rejection is the closed-enum rule of that position.
            RawUnit unarySelectorNegative = transformOps(raw, op ->
                op.kind().equals("STDLIB_CALL")
                    ? asUnaryWithSelector(op, "TIME_NOW_MILLIS") : op);
            Optional<CompilerDiagnostic> unarySelectorFailure =
                validateText(unarySelectorNegative, facts);
            check(unarySelectorFailure.isPresent(),
                "TIME_NOW_MILLIS in a UnarySelector position fails validation");
            if (unarySelectorFailure.isPresent()) {
                check(unarySelectorFailure.get().message().contains("TIME_NOW_MILLIS")
                        && (unarySelectorFailure.get().message().contains("R-ENUM")
                            || unarySelectorFailure.get().message()
                                .contains("R-RESERVED-NAME")),
                    "the rejection names the reserved value in the closed selector "
                        + "position: " + unarySelectorFailure.get().message());
            }

            // (c) TIME_NOW_MILLIS in the StdlibFunctionId position (the
            // payload function field) → R-RESERVED-NAME.
            RawUnit functionNegative = transformOps(raw, op ->
                op.kind().equals("STDLIB_CALL")
                    ? withPayloadField(op, "function", "TIME_NOW_MILLIS") : op);
            Optional<CompilerDiagnostic> functionFailure =
                validateText(functionNegative, facts);
            check(functionFailure.isPresent(),
                "TIME_NOW_MILLIS in the StdlibFunctionId position fails validation");
            if (functionFailure.isPresent()) {
                check(functionFailure.get().message().contains("R-RESERVED-NAME")
                        && functionFailure.get().message().contains("TIME_NOW_MILLIS"),
                    "the failure is R-RESERVED-NAME on the reserved function name: "
                        + functionFailure.get().message());
            }

            // (d) The reserved selector stays absent from the closed sets.
            check(StdlibFunctionId.RESERVED_NAMES.equals(List.of("TIME_NOW_MILLIS")),
                "TIME_NOW_MILLIS stays the single reserved selector name");
            boolean absentFromCatalog = true;
            for (StdlibFunctionId function : StdlibFunctionId.values()) {
                if ("TIME_NOW_MILLIS".equals(function.name())) {
                    absentFromCatalog = false;
                }
            }
            check(absentFromCatalog && StdlibFunctionId.values().length == 20,
                "TIME_NOW_MILLIS is absent from the closed 20-value StdlibFunctionId "
                    + "set");
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 5. Time-lock routing: LEGACY in every purpose, no common unit
    // =========================================================================

    static void testTimeLockRoutingNegatives() throws Exception {
        System.out.println("-- Time lock: STDLIB_TIME_CONFLICT routes LEGACY in every purpose --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-timeroute");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as t from "std/time"

                    function run(): null {
                      let n: int = t.nowMillis()
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            ModuleId mainId = moduleOf(checked.input(), "main").moduleId();
            ModuleId libId = moduleOf(checked.input(), "lib").moduleId();

            // The manifest arm: the nowMillis module claims
            // STDLIB_TIME_CONFLICT and its importer claims it by
            // propagation.
            RequirementManifestResult manifests = manifestsOf(checked, invocation());
            if (manifests == null || manifests.hasErrors()) {
                return;
            }
            SemanticRequirementManifest libManifest = manifestOf(manifests, libId);
            SemanticRequirementManifest mainManifest = manifestOf(manifests, mainId);
            check(libManifest != null && libManifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
                "the std/time.nowMillis module claims STDLIB_TIME_CONFLICT: "
                    + (libManifest == null ? "no manifest" : libManifest.capabilities()));
            check(mainManifest != null && mainManifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
                "the importing module claims STDLIB_TIME_CONFLICT by propagation: "
                    + (mainManifest == null ? "no manifest"
                        : mainManifest.capabilities()));
            check(libManifest != null && !libManifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                "the time module claims no STDLIB_SEMANTICS (std/time has no catalog "
                    + "entry): " + (libManifest == null ? "no manifest"
                        : libManifest.capabilities()));

            // Every purpose routes LEGACY, zero diagnostics, never shadow.
            for (Object[] purpose : List.<Object[]>of(
                    new Object[] {publicPreActivation(), "PUBLIC_BUILD+PRE_ACTIVATION"},
                    new Object[] {publicV12Active(CapabilityRegistry.releaseRegistry()),
                        "PUBLIC_BUILD+V1_2_ACTIVE"},
                    new Object[] {invocation(), "COMMON_SHADOW"},
                    new Object[] {legacyRegression(), "LEGACY_REGRESSION"})) {
                CompilerInvocation planInvocation = (CompilerInvocation) purpose[0];
                String what = (String) purpose[1];
                Set<ModuleId> requests = planInvocation.purpose().name().equals("COMMON_SHADOW")
                    ? Set.of(libId) : Set.of();
                RoutePlanResult planned = MigrationPlanner.planRoutes(planInvocation,
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, requests);
                check(planned != null && !planned.hasErrors() && planned.plan() != null,
                    what + ": the time module plans with zero diagnostics: "
                        + (planned == null ? "null" : planned.diagnostics()));
                if (planned == null || planned.hasErrors() || planned.plan() == null) {
                    continue;
                }
                check(planned.plan().entries().get(libId) == ModuleRoute.LEGACY
                        && planned.plan().entries().get(mainId) == ModuleRoute.LEGACY,
                    what + ": rule 2 keeps the time module and its importer LEGACY");
                check(!planned.plan().shadowModules().contains(libId),
                    what + ": the time module is never a shadow module — never "
                        + "common-lowerable even under an explicit shadow request");
            }

            // No common unit is produced for it: the forced lowering
            // fails with E6005 and the branch is never taken.
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && lowering.hasErrors() && lowering.unit() == null,
                "the forced lowering of the time module produces no unit (E6005)");
            if (lowering != null && lowering.hasErrors()) {
                check(lowering.diagnostics().stream().anyMatch(diagnostic ->
                        diagnostic.message().contains("module 'lib'")
                            && diagnostic.message().contains("CONSTRUCT_UNLOWERED")),
                    "the failure is the exact E6005 with module lib and validatorRule "
                        + "CONSTRUCT_UNLOWERED: " + lowering.diagnostics());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 6. The stdlib-export value-read disposition (D3)
    // =========================================================================

    static void testValueReadDisposition() throws Exception {
        System.out.println("-- Value-read disposition: no claim, no route rule, E6005 (D3) --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-valueread");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"

                    function run(): null {
                      let g: (x: string) => null = console.log
                      g("x")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            ModuleId mainId = moduleOf(checked.input(), "main").moduleId();
            ModuleId libId = moduleOf(checked.input(), "lib").moduleId();
            RequirementManifestResult manifests = manifestsOf(checked, invocation());
            if (manifests == null || manifests.hasErrors()) {
                return;
            }
            SemanticRequirementManifest libManifest = manifestOf(manifests, libId);
            check(libManifest != null
                    && !libManifest.capabilities().contains(
                        deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS)
                    && !libManifest.capabilities().contains(
                        deal.semantic.ir.SemanticCapability.STDLIB_TIME_CONFLICT),
                "the value read claims no stdlib capability from the read: "
                    + (libManifest == null ? "no manifest" : libManifest.capabilities()));

            // Rule 1 (legacy profile): LEGACY_REGRESSION stays LEGACY.
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(legacyRegression(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                    "rule 1: the legacy-profile purpose routes the value-read module "
                        + "LEGACY (zero diagnostics)");
            }

            // Rule 3 (PRE_ACTIVATION): the read adds no route rule and
            // pre-activation public builds stay LEGACY.
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(publicPreActivation(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY
                        && planned.plan().entries().get(mainId) == ModuleRoute.LEGACY,
                    "rule 3: the PRE_ACTIVATION public build routes the value-read "
                        + "module LEGACY with zero diagnostics (the read adds no "
                        + "route rule)");
            }

            // Rule 5 (COMMON_SHADOW shadow request): the requested module
            // is recorded shadow SHARED, and the common unit containing
            // the read fails with the exact E6005 — no reroute, no
            // within-run fallback.
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(invocation(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of(libId));
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.SHARED
                        && planned.plan().shadowModules().contains(libId),
                    "rule 5: the shadow request records the value-read module as a "
                        + "shadow SHARED entry");
                SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
                check(lowering != null && lowering.hasErrors() && lowering.unit() == null,
                    "the common unit containing the read fails with E6005 (no unit)");
                if (lowering != null && lowering.hasErrors()) {
                    check(lowering.diagnostics().stream().anyMatch(diagnostic ->
                            diagnostic.message().contains("module 'lib'")
                                && diagnostic.message().contains("CONSTRUCT_UNLOWERED")
                                && diagnostic.message().contains(
                                    "module member access 'console.log'")),
                        "the exact E6005 names module lib, validatorRule "
                            + "CONSTRUCT_UNLOWERED, and the read position: "
                            + lowering.diagnostics());
                    check(lowering.unit() == null
                            && lowering.diagnostics().size() >= 1,
                        "no unit and no fallback product exist — the failure is "
                            + "terminal for the module");
                }
            }

            // Rule 4 (V1_2_ACTIVE promotion gate): the ISSUE-0239 MODULES
            // import arm covers the value-read module — the manifest
            // claims MODULES, so with FOUNDATION_VALUES promoted alone
            // the module reroutes LEGACY at plan time (zero diagnostics,
            // never E6005); the common unit failing with E6005 is the
            // shadow-request arm above (rule 5), and no production
            // reroute or node-level fallback exists.
            CapabilityRegistry promoted = CapabilityRegistry.releaseRegistry()
                .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                    Target.LUAJIT, CapabilityRegistry.State.PROMOTED);
            CompilerInvocation activePromoted = publicV12Active(promoted);
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(activePromoted,
                    promoted, checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                    "rule 4: the value-read module's manifest claims MODULES (the "
                        + "ISSUE-0239 import arm), so the promoted profile routes it "
                        + "LEGACY at plan time (the parent verification-3 reroute): "
                        + (planned == null ? "null" : planned.diagnostics()));
                if (planned != null && !planned.hasErrors() && planned.plan() != null) {
                    check(planned.diagnostics().isEmpty()
                            && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                        "the route is LEGACY with zero diagnostics — the plan-time "
                            + "reroute, never E6005 and never a node-level fallback");
                }
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 7. Rule 4's promotion gate covers stdlib-using modules
    // =========================================================================

    static void testRouteRule4PromotionGateCoversStdlibModules() throws Exception {
        System.out.println("-- Rule 4: the promotion gate covers stdlib-using modules --");

        Path tmp = Files.createTempDirectory("deal-stdlib-claim-rule4");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
                "main.deal", """
                    import * as lib from "./lib"

                    export function main(): null {
                      return null
                    }
                    """,
                "lib.deal", """
                    import * as console from "std/console"

                    function run(): null {
                      console.log("x")
                      return null
                    }

                    function main(): null {
                      run()
                      return null
                    }
                    """), "main.deal");
            if (checked == null) {
                return;
            }
            ModuleId libId = moduleOf(checked.input(), "lib").moduleId();
            RequirementManifestResult manifests = manifestsOf(checked, invocation());
            if (manifests == null || manifests.hasErrors()) {
                return;
            }
            SemanticRequirementManifest libManifest = manifestOf(manifests, libId);
            check(libManifest != null && libManifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                "the stdlib-calling module's manifest carries the plan-time "
                    + "STDLIB_SEMANTICS claim: " + (libManifest == null ? "none"
                        : libManifest.capabilities()));

            // With STDLIB_SEMANTICS shadowed the promotion gate reroutes
            // LEGACY silently (zero diagnostics, never an error).
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(
                    publicV12Active(CapabilityRegistry.releaseRegistry()),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                    "rule 4 reroutes the stdlib module LEGACY while STDLIB_SEMANTICS "
                        + "is shadowed (silent, zero diagnostics)");
            }

            // The fixture's non-exported `main` is never called from
            // source, so the ISSUE-0239 never-called arm claims CALLS
            // too (an uncalled non-exported declared function cannot
            // lower under the statically-resolved call machine — an
            // over-claim only forces LEGACY).
            check(libManifest != null && libManifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.CALLS),
                "the fixture's manifest carries the ISSUE-0239 CALLS claim "
                    + "(the uncalled non-exported main): "
                    + (libManifest == null ? "none" : libManifest.capabilities()));

            // With FOUNDATION_VALUES + STDLIB_SEMANTICS + MODULES +
            // CALLS promoted the module routes SHARED — the plan-time
            // claims (the stdlib arm, the ISSUE-0239 import arm, and the
            // never-called arm) made the gate cover it before lowering.
            CapabilityRegistry promoted = CapabilityRegistry.releaseRegistry()
                .withState(deal.semantic.ir.SemanticCapability.FOUNDATION_VALUES,
                    Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
                .withState(deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS,
                    Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
                .withState(deal.semantic.ir.SemanticCapability.MODULES,
                    Target.LUAJIT, CapabilityRegistry.State.PROMOTED)
                .withState(deal.semantic.ir.SemanticCapability.CALLS,
                    Target.LUAJIT, CapabilityRegistry.State.PROMOTED);
            CompilerInvocation activePromoted = publicV12Active(promoted);
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(activePromoted,
                    promoted, checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.SHARED,
                    "rule 4 routes the stdlib module SHARED once every manifest "
                        + "capability (STDLIB_SEMANTICS + MODULES + CALLS) is "
                        + "promoted for the target: "
                        + (planned == null ? "null" : planned.diagnostics()));
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 8. Combined T4 behavior: the exact projections + the manifest claim
    // =========================================================================

    /** One lowered-and-validated stdlib scenario unit. */
    private record Scenario(LoweredModuleUnit unit, StructuredBodyTable table,
                            CheckedProjectBuildResult checked,
                            SemanticRequirementManifest manifest, Path tmp) {
    }

    /**
     * Compiles + lowers one scenario in the two-module carrier shape: the
     * entry module "main.deal" (exported main, never lowered) and the
     * subject "lib.deal" whose plain functions carry the stdlib calls.
     * Asserts the same module's plan-time manifest claims
     * STDLIB_SEMANTICS — the T5 arm over the T2/T1 production.
     */
    private static Scenario lowerScenario(String libSource, String what) {
        try {
            Path tmp = Files.createTempDirectory("deal-stdlib-claim-combined");
            Path src = tmp.resolve("src");
            Files.createDirectories(src);
            Files.writeString(src.resolve("main.deal"), """
                import * as lib from "./lib"

                export function main(): null {
                  return null
                }
                """);
            Files.writeString(src.resolve("lib.deal"), libSource);
            CompilationOrchestrator orchestrator = new CompilationOrchestrator(
                src.resolve("main.deal").toAbsolutePath(), tmp.resolve("build"), false, false, false, false, Backend.LUAJIT,
                null, List.of(src.toAbsolutePath()),
                Path.of("std").toAbsolutePath().normalize(), null, ConformanceHarnessMetadata.invocation(SemanticProfile.DEAL_V1_2_INT32));
            boolean ok = orchestrator.compile();
            check(ok, what + ": compiles through phase 3 + builder: "
                + orchestrator.diagnostics());
            if (!ok) {
                return null;
            }
            CheckedProjectBuildResult checked = orchestrator.checkedProject();
            if (checked == null || checked.hasErrors() || checked.input() == null) {
                fail(what + ": no clean checked project");
                return null;
            }
            CheckedModuleInput subject = null;
            for (CheckedModuleInput module : checked.input().modules()) {
                if (module.moduleId().path().equals("lib")) {
                    subject = module;
                }
            }
            if (subject == null) {
                fail(what + ": no lib module in the checked project");
                return null;
            }
            RequirementManifestResult manifests = LoweringSupport.computeManifests(
                invocation(), checked.input(), checked.index());
            if (manifests == null || manifests.hasErrors()
                    || manifests.manifests() == null || manifests.manifests().isEmpty()) {
                fail(what + ": no clean manifest: "
                    + (manifests == null ? "null" : manifests.diagnostics()));
                return null;
            }
            SemanticRequirementManifest manifest = manifestOf(manifests,
                subject.moduleId());
            if (manifest == null) {
                fail(what + ": no manifest for lib");
                return null;
            }
            check(manifest.capabilities().contains(
                    deal.semantic.ir.SemanticCapability.STDLIB_SEMANTICS),
                what + ": the same module's manifest claims STDLIB_SEMANTICS (the "
                    + "plan-time arm over the produced STDLIB_CALLs): "
                    + manifest.capabilities());
            List<ModuleId> moduleIds = new ArrayList<>();
            for (CheckedModuleInput module : checked.input().modules()) {
                moduleIds.add(module.moduleId());
            }
            SemanticLowerer.LoweringResult lowering = SemanticLowerer.lowerModuleFullProgram(
                subject, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
                checked.index().interfaceIndexDigest(),
                CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
                SemanticIdAllocator.over(moduleIds));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                fail(what + ": lowering failed: " + (lowering == null ? "null"
                    : lowering.diagnostics()));
                return null;
            }
            return new Scenario(lowering.unit(), lowering.table(), checked, manifest, tmp);
        } catch (Exception e) {
            fail(what + ": scenario setup threw: " + e);
            return null;
        }
    }

    /** The canonical origin atom of an op (sourceId:line:column). */
    private static String originAtomOf(SemanticOp op) {
        SourceOrigin origin = op.origin();
        SourceSpan span = origin.span();
        return SemanticRuntimeModel.originAtom(origin.sourceId(),
            span == null ? null : span.startLine(),
            span == null ? null : span.startColumn());
    }

    /** The FunctionId whose body block contains the op, or null. */
    private static FunctionId owningFunctionOf(Scenario scenario, SemanticOp op) {
        for (Map.Entry<FunctionId, LoweredFunction> entry
                : scenario.unit().functions().entrySet()) {
            List<OpId> bodyOps = scenario.table().blockOps().get(entry.getValue().body());
            if (bodyOps != null && bodyOps.contains(op.opId())) {
                return entry.getKey();
            }
        }
        return null;
    }

    /** The expected frame id strings of a failure inside the op's owning
     *  function: the active direct-call chain innermost-first. */
    private static List<String> expectedFrames(Scenario scenario, SemanticOp call) {
        LoweredModuleUnit unit = scenario.unit();
        Map<FunctionId, FunctionId> callerOf = new LinkedHashMap<>();
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CALL
                    && op.payload() instanceof KindPayload.CallPayload callPayload
                    && callPayload.callee() instanceof KindPayload.CallCallee.Static
                        staticCallee
                    && staticCallee.binding()
                        instanceof FunctionExecutionBinding.LoweredBody body) {
                FunctionId caller = owningFunctionOf(scenario, op);
                if (caller != null) {
                    callerOf.put(body.functionId(), caller);
                }
            }
        }
        List<String> frames = new ArrayList<>();
        FunctionId current = owningFunctionOf(scenario, call);
        while (current != null) {
            frames.add(String.valueOf(current.id()));
            current = callerOf.get(current);
        }
        return frames;
    }

    /** The synthetic primitive-level operation origin. */
    private static SourceOrigin origin() {
        return new SourceOrigin("stdlib-claiming-test", SourceSpan.synthetic("stdlib"),
            deal.semantic.ir.SourceOriginKind.SYNTHETIC,
            new deal.semantic.ir.AnchorId(1), null);
    }

    /** The scalar-valid carrier of a test string. */
    private static UnicodeScalars.Valid valid(String text) {
        return (UnicodeScalars.Valid) UnicodeScalars.validate(text);
    }

    static void testCombinedT4Behavior() {
        System.out.println("-- Combined T4 behavior: exact projections + the manifest claim --");

        // The primitive-level projections of the two named defects (the
        // T4 wiring, driven directly before the oracle run).
        {
            Outcome<SharedStdlibSemantics.Value> parse = SharedStdlibSemantics.jsonParse(
                origin(), valid("x"));
            check(parse instanceof Outcome.Failure<SharedStdlibSemantics.Value>,
                "jsonParse(\"x\") fails through the shared algorithm");
            if (parse instanceof Outcome.Failure<SharedStdlibSemantics.Value> failure) {
                StdlibFailure stdlibFailure = failure.failure();
                BoundaryFailure projection = stdlibFailure.failure();
                FailurePolicyRow row = FailureContractRegistry.row(
                    FailurePolicyId.JSON_PARSE_SYNTAX);
                String expectedMessage = BoundaryFailure.fromRow(row, 0, null, null,
                    Map.of("oneBasedByteOffset", "1", "reason",
                        SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER), null).message();
                check(projection.policy() == FailurePolicyId.JSON_PARSE_SYNTAX
                        && projection.code() == DiagnosticCode.E8001
                        && projection.message().equals(expectedMessage)
                        && projection.metadata().equals(Map.of(
                            "oneBasedByteOffset", "1",
                            "reason", SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER))
                        && projection.cause() == null
                        && stdlibFailure.origin().equals(origin()),
                    "the JSON_PARSE_SYNTAX projection carries the exact template, the "
                        + "two-key metadata, no cause, and the call origin");
            }

            Outcome<SharedStdlibSemantics.Value> abs = SharedStdlibSemantics.mathAbsInt(
                origin(), -2147483648);
            check(abs instanceof Outcome.Failure<SharedStdlibSemantics.Value>,
                "absInt(-2147483648) fails through the shared algorithm");
            if (abs instanceof Outcome.Failure<SharedStdlibSemantics.Value> failure) {
                BoundaryFailure projection = failure.failure().failure();
                check(projection.policy() == FailurePolicyId.INT32_RESULT
                        && projection.code() == DiagnosticCode.E8004
                        && projection.message().equals("int out of range")
                        && projection.metadata().isEmpty()
                        && failure.failure().origin().equals(origin()),
                    "the INT32_RESULT projection is exactly E8004 'int out of range' "
                        + "at the call origin");
            }
        }

        // (a) JSON_PARSE on a syntax-defect input through the oracle:
        // the resolved record equals the exact canonical projection.
        Scenario syntax = lowerScenario("""
            import * as json from "std/json"

            function helper(): null {
              let t: table = json.parse("x")
              return null
            }

            function main(): null {
              helper()
              return null
            }
            """, "the syntax-defect scenario");
        if (syntax != null) {
            SemanticOp call = stdlibOpBy(syntax.unit(), StdlibFunctionId.JSON_PARSE);
            check(call != null, "the syntax scenario lowers one JSON_PARSE STDLIB_CALL");
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(syntax.unit(), syntax.table());
                if (run.terminal()
                        instanceof SemanticRuntimeModel.Terminal.DealFailure terminal) {
                    SemanticRuntimeModel.ErrorSnapshot error = terminal.error();
                    check(error.code().equals("E8001")
                            && error.message().equals(
                                "JSON parse error at position 1: unexpected character")
                            && error.origin().equals(originAtomOf(call))
                            && error.frames().equals(expectedFrames(syntax, call))
                            && error.cause() == null,
                        "the oracle terminal is the exact JSON_PARSE_SYNTAX projection "
                            + "at the call origin with the active frames and no cause: "
                            + error);
                } else {
                    fail("the syntax scenario expected a DealFailure terminal, got "
                        + run.terminal());
                }
            }
            deleteRecursively(syntax.tmp());
        }

        // (b) MATH_ABS_INT(-2147483648) through the oracle: E8004 at the
        // call origin.
        Scenario abs = lowerScenario("""
            import * as math from "std/math"

            function main(): null {
              let x: int = -2147483647 - 1
              let n: int = math.absInt(x)
              return null
            }
            """, "the absInt-min scenario");
        if (abs != null) {
            SemanticOp call = stdlibOpBy(abs.unit(), StdlibFunctionId.MATH_ABS_INT);
            check(call != null, "the abs scenario lowers one MATH_ABS_INT STDLIB_CALL");
            if (call != null) {
                SemanticRuntimeModel.ConsumerRun run =
                    SemanticOracle.execute(abs.unit(), abs.table());
                if (run.terminal()
                        instanceof SemanticRuntimeModel.Terminal.DealFailure terminal) {
                    SemanticRuntimeModel.ErrorSnapshot error = terminal.error();
                    check(error.code().equals("E8004")
                            && error.message().equals("int out of range")
                            && error.origin().equals(originAtomOf(call))
                            && error.frames().equals(expectedFrames(abs, call))
                            && error.cause() == null,
                        "the oracle terminal is the exact INT32_RESULT projection at "
                            + "the call origin with the active frames: " + error);
                } else {
                    fail("the abs scenario expected a DealFailure terminal, got "
                        + run.terminal());
                }
            }
            deleteRecursively(abs.tmp());
        }
    }

    // =========================================================================
    // 9. Retained-time regression: unchanged pins + the live probe
    // =========================================================================

    static void testRetainedTimeRegression() {
        System.out.println("-- Retained-time regression: unchanged pins, live probe --");

        try {
            // std/time.lua stays byte-identical — no time algorithm, no
            // time projection, and no nowMillis decision land here.
            String timeLua = Files.readString(Path.of("std/time.lua"));
            String pinnedTimeLua = """
                -- DEAL Standard Library: std/time
                -- Provides time-related functions.

                local __rt = require("deal.runtime")

                local time = {}

                --- Returns the current Unix timestamp in milliseconds as an int.
                time.nowMillis = __rt.function_("()->int", function()
                  return __rt.check_int(os.time() * 1000)
                end)

                return time
                """;
            check(timeLua.equals(pinnedTimeLua),
                "std/time.lua is unchanged (byte-identical to the pinned retained "
                    + "content)");


            // The live retained behavior probe: the gate's own luajit
            // leg replicates the retained std/time surface — E8004 under
            // the signed-int32 gate (the landed disposition), unchanged.
            boolean luajitAvailable = false;
            try {
                new ProcessBuilder("luajit", "-v").start().waitFor();
                luajitAvailable = true;
            } catch (IOException e) {
                // environment without luajit — the pin assertions above
                // carry the regression coverage
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            if (luajitAvailable) {
                String probe = """
                    package.path = "./?.lua;./?/init.lua;" .. package.path
                    local timelib = require("std.time")
                    local ok, err = pcall(function() timelib.nowMillis.f() end)
                    if ok then
                      print("BROKEN: nowMillis succeeded under the retained gate")
                      os.exit(1)
                    end
                    local code = type(err) == "table" and err.code
                    if code ~= "E8004" then
                      print("BROKEN: nowMillis code = " .. tostring(code))
                      os.exit(1)
                    end
                    print("time-lock-ok")
                    """;
                Process process = new ProcessBuilder("luajit", "-e", probe)
                    .redirectErrorStream(true).start();
                String out = new String(process.getInputStream().readAllBytes(),
                    StandardCharsets.UTF_8);
                int exit = process.waitFor();
                check(exit == 0 && out.contains("time-lock-ok"),
                    "the retained std/time.lua behavior stays green under its "
                        + "existing authority (E8004 gate): " + out.trim());
            }
        } catch (Exception e) {
            fail("the retained-time regression threw: " + e);
        }
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Stdlib Claiming / Time-Lock Tests (ISSUE-0497) ===\n");

        testHomeRowsArmAndDerivation();
        testManifestArm();
        testRCapabilityNegatives();
        testTimeLockValidatorNegatives();
        testTimeLockRoutingNegatives();
        testValueReadDisposition();
        testRouteRule4PromotionGateCoversStdlibModules();
        testCombinedT4Behavior();
        testRetainedTimeRegression();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
