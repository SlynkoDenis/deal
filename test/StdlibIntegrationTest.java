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
import deal.semantic.SharedStdlibSemantics.Channel;
import deal.semantic.SharedStdlibSemantics.ConsoleSink;
import deal.semantic.SharedStdlibSemantics.Outcome;
import deal.semantic.SharedStdlibSemantics.Value;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.Target;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FailurePolicyRow;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RawOp;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.UnicodeScalars;
import deal.types.Type;

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
 * The ISSUE-0499 decomposition tail: the end-to-end stdlib and time-lock
 * integration verification. One pipeline drives the six landed
 * constituents in order — T1 the closed {@link StdlibFunctionCatalog}
 * lookup, T2 the checked-fact recognition plus the {@code STDLIB_CALL}
 * lowering arm producing one validated op per closed id, T3 the
 * {@link SharedStdlibSemantics} execution of every id with the named
 * edge cases, T4 the exact resolved projections, T5 the
 * {@code STDLIB_SEMANTICS} claiming seam plus the time-lock and D3
 * negatives — and fails the run with the first failing constituent named when any
 * of them is broken ({@code stdlib-operations-and-time-lock} Contracts
 * §Integration verification task, Verification 7-8).
 *
 * <p><b>All-constituents contract.</b> The pipeline accepts an injected
 * {@link Fault}; every injected-fault variant — a dropped catalog
 * entry, a misstamped failure policy, a changed trim-set edge, a
 * tampered JSON projection template, and a dropped {@code STDLIB_CALL}
 * home row — must flip the pipeline to failure with the broken
 * constituent and the exact expected-versus-actual mismatch named. No
 * constituent may silently pass.</p>
 *
 * <p><b>Determinism.</b> The task is single-threaded and deterministic:
 * every phase reads pinned fixtures and the landed production seams.
 * Cross-runtime helper equivalence remains owned by the dedicated battery;
 * this integration test does not duplicate its registry or execution.</p>
 */
public final class StdlibIntegrationTest {

    private StdlibIntegrationTest() {
        // Static test main only.
    }

    // =========================================================================
    // Harness
    // =========================================================================

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

    // =========================================================================
    // The injected-fault model and the pipeline report
    // =========================================================================

    /**
     * One injected constituent break for the all-constituents contract:
     * each maps to exactly one pipeline phase and must flip the clean
     * pipeline to failure with that constituent named.
     */
    private enum Fault {
        NONE,
        /** T1: the catalog loses the {@code std.string.trim} row. */
        CATALOG_DROP,
        /** T2: the {@code STRING_TRIM} op stamps the wrong failure policy. */
        POLICY_MISSTAMP,
        /** T3: the trim algorithm widens the closed set with U+00A0. */
        TRIM_TAMPER,
        /** T4: the JSON_PARSE_SYNTAX projection carries a tampered {@code {reason}}. */
        PROJECTION_TAMPER,
        /** T5: the {@code STDLIB_CALL → STDLIB_SEMANTICS} home row is dropped. */
        HOME_ROW_DROP
    }

    /** One pipeline run: the overall verdict plus the first failing constituent. */
    private record PipelineReport(boolean ok, String firstFailure) {
    }

    /** Counts a real defect and returns the failed phase report. */
    private static PipelineReport defect(String detail) {
        fail(detail);
        return new PipelineReport(false, detail);
    }

    /** Returns the failed phase report of an injected fault (expected, uncounted). */
    private static PipelineReport injectedFault(String detail) {
        return new PipelineReport(false, detail);
    }

    // =========================================================================
    // The pinned outcome and seed model (the hand-pinned parent table)
    // =========================================================================

    /** The pinned expected outcome of one execution seed. */
    private sealed interface Pinned
        permits Pinned.PinnedSuccess, Pinned.PinnedFailure {

        record PinnedSuccess(Value value) implements Pinned {
            public PinnedSuccess {
                java.util.Objects.requireNonNull(value, "value must not be null");
            }
        }

        record PinnedFailure(FailurePolicyId policy, DiagnosticCode code, String message,
                             String expectedText, String actualText,
                             Map<String, String> metadata) implements Pinned {

            public PinnedFailure {
                java.util.Objects.requireNonNull(policy, "policy must not be null");
                java.util.Objects.requireNonNull(code, "code must not be null");
                java.util.Objects.requireNonNull(message, "message must not be null");
                metadata = Map.copyOf(metadata);
            }
        }
    }

    /** One execution seed: the id, the declared-descriptor argument values, the pinned outcome. */
    private record Seed(StdlibFunctionId function, List<Value> args, Pinned outcome) {
        public Seed {
            args = List.copyOf(args);
            java.util.Objects.requireNonNull(outcome, "outcome must not be null");
        }
    }

    private static Value s(String text) {
        return Value.string(text);
    }

    private static Value i(int value) {
        return new Value.Int(value);
    }

    private static Value n(double value) {
        return new Value.Number(value);
    }

    private static Value b(boolean value) {
        return new Value.Bool(value);
    }

    private static final Value NULL = Value.Null.INSTANCE;

    private static Value arr(String... elements) {
        List<Value> values = new ArrayList<>();
        for (String element : elements) {
            values.add(s(element));
        }
        return Value.array(values);
    }

    private static Value tableOf(List<String> keys, List<Value> values) {
        SemanticTable<Value> table = new SemanticTable<>();
        for (int index = 0; index < keys.size(); index++) {
            table.put(keys.get(index), values.get(index));
        }
        return new Value.Table(table);
    }

    private static Pinned ok(Value value) {
        return new Pinned.PinnedSuccess(value);
    }

    private static Pinned fail(FailurePolicyId policy, DiagnosticCode code, String message,
                               String expectedText, String actualText, String... metadataPairs) {
        Map<String, String> metadata = new LinkedHashMap<>();
        for (int index = 0; index + 1 < metadataPairs.length; index += 2) {
            metadata.put(metadataPairs[index], metadataPairs[index + 1]);
        }
        return new Pinned.PinnedFailure(policy, code, message, expectedText, actualText,
            metadata);
    }

    private static Seed seed(StdlibFunctionId function, List<Value> args, Pinned outcome) {
        return new Seed(function, args, outcome);
    }

    /** Deep structural equality over the closed value view (numbers via {@code Double.compare}). */
    private static boolean valueEquals(Value a, Value b) {
        if (a == b) {
            return true;
        }
        if (a.getClass() != b.getClass()) {
            return false;
        }
        return switch (a) {
            case Value.Null ignored -> true;
            case Value.Bool bool -> bool.value() == ((Value.Bool) b).value();
            case Value.Int intValue -> intValue.value() == ((Value.Int) b).value();
            case Value.Number number ->
                Double.compare(number.value(), ((Value.Number) b).value()) == 0;
            case Value.String string -> {
                UnicodeScalars.ScalarString left = string.scalar();
                UnicodeScalars.ScalarString right = ((Value.String) b).scalar();
                yield left instanceof UnicodeScalars.Invalid
                    ? right instanceof UnicodeScalars.Invalid
                    : right instanceof UnicodeScalars.Valid valid
                        && ((UnicodeScalars.Valid) left).carrier().equals(valid.carrier());
            }
            case Value.Table table -> {
                SemanticTable<Value> left = table.table();
                SemanticTable<Value> right = ((Value.Table) b).table();
                if (!left.keys().equals(right.keys())) {
                    yield false;
                }
                boolean equal = true;
                for (String key : left.keys()) {
                    SemanticTable.Lookup<Value> leftLookup = left.get(key);
                    SemanticTable.Lookup<Value> rightLookup = right.get(key);
                    if (!(leftLookup instanceof SemanticTable.Lookup.Present<Value> leftPresent)
                            || !(rightLookup
                                instanceof SemanticTable.Lookup.Present<Value> rightPresent)
                            || !valueEquals(leftPresent.value(), rightPresent.value())) {
                        equal = false;
                        break;
                    }
                }
                yield equal;
            }
            case Value.Array array -> {
                SemanticArray<Value> left = array.elements();
                SemanticArray<Value> right = ((Value.Array) b).elements();
                if (left.size() != right.size()) {
                    yield false;
                }
                boolean equal = true;
                for (int index = 0; index < left.size(); index++) {
                    if (!valueEquals(left.elementAt(index), right.elementAt(index))) {
                        equal = false;
                        break;
                    }
                }
                yield equal;
            }
            case Value.Other other -> other.kind() == ((Value.Other) b).kind()
                && java.util.Objects.equals(other.classId(), ((Value.Other) b).classId());
        };
    }

    private static String describeValue(Value value) {
        return switch (value) {
            case Value.Null ignored -> "null";
            case Value.Bool bool -> Boolean.toString(bool.value());
            case Value.Int intValue -> Integer.toString(intValue.value());
            case Value.Number number -> Double.toString(number.value());
            case Value.String string -> string.scalar() instanceof UnicodeScalars.Valid valid
                ? "'" + valid.carrier() + "'" : "invalid-scalar";
            case Value.Table table -> "table" + table.table().keys();
            case Value.Array array -> "array(" + array.elements().size() + ")";
            case Value.Other other -> other.kind().name();
        };
    }

    private static String describePinned(Pinned pinned) {
        return switch (pinned) {
            case Pinned.PinnedSuccess(Value value) -> "Success(" + describeValue(value) + ")";
            case Pinned.PinnedFailure(FailurePolicyId policy, DiagnosticCode code,
                                      String message, String expectedText, String actualText,
                                      Map<String, String> metadata) ->
                "Failure(" + policy + " " + code + " '" + message + "' expected="
                    + expectedText + " actual=" + actualText + " metadata=" + metadata + ")";
        };
    }

    private static String describeOutcome(Outcome<Value> outcome) {
        return switch (outcome) {
            case Outcome.Success<Value> success -> "Success("
                + describeValue(success.value()) + ")";
            case Outcome.Failure<Value> failure -> "Failure("
                + failure.failure().failure().policy() + " "
                + failure.failure().failure().code() + " '"
                + failure.failure().failure().message() + "' expected="
                + failure.failure().failure().expected() + " actual="
                + failure.failure().failure().actual() + " metadata="
                + failure.failure().failure().metadata() + ")";
        };
    }

    /** True when the execution outcome matches the pinned parent-table expectation. */
    private static boolean pinnedMatches(Outcome<Value> outcome, Pinned pinned,
                                         SourceOrigin origin) {
        return switch (pinned) {
            case Pinned.PinnedSuccess(Value expected) ->
                outcome instanceof Outcome.Success<Value> success
                    && valueEquals(success.value(), expected);
            case Pinned.PinnedFailure(FailurePolicyId policy, DiagnosticCode code,
                                      String message, String expectedText, String actualText,
                                      Map<String, String> metadata) ->
                outcome instanceof Outcome.Failure<Value> failure
                    && failure.failure().failure().policy() == policy
                    && failure.failure().failure().code() == code
                    && failure.failure().failure().message().equals(message)
                    && java.util.Objects.equals(failure.failure().failure().expected(),
                        expectedText)
                    && java.util.Objects.equals(failure.failure().failure().actual(),
                        actualText)
                    && failure.failure().failure().metadata().equals(metadata)
                    && failure.failure().failure().cause() == null
                    && failure.failure().origin().equals(origin);
        };
    }

    // =========================================================================
    // The fixed operation origin and declared descriptors
    // =========================================================================

    private static final RuntimeDescriptor DESC_STRING =
        deal.semantic.DescriptorService.describe(Type.String.INSTANCE);
    private static final RuntimeDescriptor DESC_TABLE =
        deal.semantic.DescriptorService.describe(Type.Table.INSTANCE);

    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    private static StdlibFunctionCatalog.Entry catalogEntryOf(StdlibFunctionId function) {
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            if (entry.function() == function) {
                return entry;
            }
        }
        throw new IllegalStateException("no catalog row for " + function);
    }

    // =========================================================================
    // Shared fixtures
    // =========================================================================

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

    /** The fixed common-shadow invocation of the carrier drives. */
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
     * production carrier (manifests → full-program lowerer → validator).
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

    /** The child ops of the given op (origin.parentOpId = opId) in unit order. */
    private static List<SemanticOp> childrenOf(LoweredModuleUnit unit, OpId parent) {
        List<SemanticOp> children = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            if (parent.equals(op.origin().parentOpId())) {
                children.add(op);
            }
        }
        return children;
    }

    /** The canonical origin atom of an op (sourceId:line:column). */
    private static String originAtomOf(SemanticOp op) {
        SourceOrigin origin = op.origin();
        SourceSpan span = origin.span();
        return SemanticRuntimeModel.originAtom(origin.sourceId(),
            span == null ? null : span.startLine(),
            span == null ? null : span.startColumn());
    }

    // =========================================================================
    // The corpus: one checked project carrying one call per closed id
    // =========================================================================

    private static Map<String, String> corpusSources() {
        return Map.of(
            "main.deal", """
                import * as lib from "./lib"
                import * as plain from "./plain"
                import * as trivial from "./trivial"

                export function main(): null {
                  return null
                }
                """,
            "lib.deal", """
                import * as console from "std/console"
                import * as str from "std/string"
                import * as tbl from "std/table"
                import * as json from "std/json"
                import * as math from "std/math"

                function run(): null {
                  console.log("log")
                  console.error("error")
                  let n1: int = str.length("héllo 😀")
                  let s2: string = str.substring("😀a", -5, 1)
                  let b3: boolean = str.contains("abc", "")
                  let b4: boolean = str.startsWith("abc", "ab")
                  let b5: boolean = str.endsWith("abc", "bc")
                  let s6: string = str.replace("aaa", "aa", "b")
                  let xs7: string[] = str.split("a,,b", ",")
                  let s8: string = str.trim(" x ")
                  let t: table = {a: 1, b: 2}
                  let ks9: string[] = tbl.keys(t)
                  let jt10: table = json.parse("{\\"a\\":1,\\"a\\":2}")
                  let js11: string = json.stringify(t)
                  let f12: number = math.floor(1.5)
                  let f13: number = math.ceil(1.5)
                  let f14: number = math.sqrt(4.0)
                  let i15: int = math.absInt(-3)
                  let f16: number = math.absNumber(-1.5)
                  let i17: int = math.minInt(2, 2)
                  let i18: int = math.maxInt(-1, -2)
                  return null
                }

                function main(): null {
                  run()
                  return null
                }
                """,
            "util.deal", """
                export function length(s: string): int {
                  return 0
                }
                """,
            "plain.deal", """
                import * as s from "./util"

                function run(): null {
                  s.length("x")
                  return null
                }

                function main(): null {
                  run()
                  return null
                }
                """,
            "trivial.deal", """
                function run(): null {
                  let n: int = 1
                  return null
                }

                function main(): null {
                  run()
                  return null
                }
                """);
    }

    /** The closed 20-id seed table with the named acceptance edge cases. */
    private static List<Seed> seeds() {
        List<Seed> seeds = new ArrayList<>();

        // ---- console: byte-exact effects + null result (asserted on the sink) ----
        seeds.add(seed(StdlibFunctionId.CONSOLE_LOG, List.of(s("")), ok(NULL)));
        seeds.add(seed(StdlibFunctionId.CONSOLE_LOG, List.of(s("héllo 😀")), ok(NULL)));
        seeds.add(seed(StdlibFunctionId.CONSOLE_ERROR, List.of(s("err")), ok(NULL)));

        // ---- string length: Unicode scalar count (empty, multi-scalar) ----
        seeds.add(seed(StdlibFunctionId.STRING_LENGTH, List.of(s("")), ok(i(0))));
        seeds.add(seed(StdlibFunctionId.STRING_LENGTH, List.of(s("abc")), ok(i(3))));
        seeds.add(seed(StdlibFunctionId.STRING_LENGTH, List.of(s("héllo")), ok(i(5))));
        seeds.add(seed(StdlibFunctionId.STRING_LENGTH, List.of(s("😀")), ok(i(1))));
        seeds.add(seed(StdlibFunctionId.STRING_LENGTH, List.of(s("a😀b")), ok(i(3))));

        // ---- substring: scalar clamping to [lo,hi) ----
        seeds.add(seed(StdlibFunctionId.STRING_SUBSTRING,
            List.of(s("abc"), i(0), i(3)), ok(s("abc"))));
        seeds.add(seed(StdlibFunctionId.STRING_SUBSTRING,
            List.of(s("abc"), i(0), i(-1)), ok(s(""))));
        seeds.add(seed(StdlibFunctionId.STRING_SUBSTRING,
            List.of(s("abc"), i(-2), i(2)), ok(s("ab"))));
        seeds.add(seed(StdlibFunctionId.STRING_SUBSTRING,
            List.of(s("abc"), i(2), i(2)), ok(s(""))));
        seeds.add(seed(StdlibFunctionId.STRING_SUBSTRING,
            List.of(s("😀a"), i(-5), i(1)), ok(s("😀"))));

        // ---- contains/prefix/suffix: empty part is contained, prefix, suffix ----
        seeds.add(seed(StdlibFunctionId.STRING_CONTAINS,
            List.of(s("abc"), s("")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_CONTAINS,
            List.of(s(""), s("")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_CONTAINS,
            List.of(s("abc"), s("d")), ok(b(false))));
        seeds.add(seed(StdlibFunctionId.STRING_CONTAINS,
            List.of(s("a😀b"), s("😀")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_STARTS_WITH,
            List.of(s("abc"), s("ab")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_STARTS_WITH,
            List.of(s(""), s("")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_STARTS_WITH,
            List.of(s("abc"), s("b")), ok(b(false))));
        seeds.add(seed(StdlibFunctionId.STRING_ENDS_WITH,
            List.of(s("abc"), s("bc")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_ENDS_WITH,
            List.of(s("abc"), s("")), ok(b(true))));
        seeds.add(seed(StdlibFunctionId.STRING_ENDS_WITH,
            List.of(s("abc"), s("a")), ok(b(false))));

        // ---- replace: non-overlapping, empty from, literal replacement ----
        seeds.add(seed(StdlibFunctionId.STRING_REPLACE,
            List.of(s("aba"), s("a"), s("z")), ok(s("zbz"))));
        seeds.add(seed(StdlibFunctionId.STRING_REPLACE,
            List.of(s("aaa"), s("aa"), s("b")), ok(s("ba"))));
        seeds.add(seed(StdlibFunctionId.STRING_REPLACE,
            List.of(s("abc"), s(""), s("x")), ok(s("abc"))));
        seeds.add(seed(StdlibFunctionId.STRING_REPLACE,
            List.of(s("100%"), s("%"), s("p")), ok(s("100p"))));

        // ---- split: empty input/separator, preserved empty parts, multi-scalar ----
        seeds.add(seed(StdlibFunctionId.STRING_SPLIT,
            List.of(s(""), s(",")), ok(arr())));
        seeds.add(seed(StdlibFunctionId.STRING_SPLIT,
            List.of(s("a,b"), s(",")), ok(arr("a", "b"))));
        seeds.add(seed(StdlibFunctionId.STRING_SPLIT,
            List.of(s("a,,b"), s(",")), ok(arr("a", "", "b"))));
        seeds.add(seed(StdlibFunctionId.STRING_SPLIT,
            List.of(s("abc"), s("")), ok(arr("a", "b", "c"))));
        seeds.add(seed(StdlibFunctionId.STRING_SPLIT,
            List.of(s("😀a"), s("")), ok(arr("😀", "a"))));

        // ---- trim: exactly U+0009–U+000D and U+0020; U+00A0 is NOT trimmed ----
        seeds.add(seed(StdlibFunctionId.STRING_TRIM, List.of(s("  x  ")), ok(s("x"))));
        seeds.add(seed(StdlibFunctionId.STRING_TRIM, List.of(s("")), ok(s(""))));
        seeds.add(seed(StdlibFunctionId.STRING_TRIM,
            List.of(s("\t\n\u000b\f\r x \t\n\u000b\f\r")), ok(s("x"))));
        seeds.add(seed(StdlibFunctionId.STRING_TRIM,
            List.of(s("\u00a0x\u00a0")), ok(s("\u00a0x\u00a0"))));
        seeds.add(seed(StdlibFunctionId.STRING_TRIM, List.of(s("a\tb")), ok(s("a\tb"))));

        // ---- table keys: first-insertion order, delete-reinsert-to-end ----
        seeds.add(new Seed(StdlibFunctionId.TABLE_KEYS,
            List.of(tableOf(List.of(), List.of())), ok(arr())));
        seeds.add(new Seed(StdlibFunctionId.TABLE_KEYS,
            List.of(tableOf(List.of("a", "b", "c"), List.of(i(1), i(2), i(3)))),
            ok(arr("a", "b", "c"))));
        {
            SemanticTable<Value> table = new SemanticTable<>();
            table.put("a", i(1));
            table.put("b", i(2));
            table.put("c", i(3));
            table.remove("a");
            table.put("a", i(9));
            seeds.add(new Seed(StdlibFunctionId.TABLE_KEYS,
                List.of(new Value.Table(table)), ok(arr("b", "c", "a"))));
        }

        // ---- json parse: duplicate keys (last value, first position),
        //      signed32 lexical int mapping, syntax failure ----
        seeds.add(new Seed(StdlibFunctionId.JSON_PARSE,
            List.of(s("{\"a\":1,\"a\":2}")),
            ok(tableOf(List.of("a"), List.of(i(2))))));
        seeds.add(new Seed(StdlibFunctionId.JSON_PARSE,
            List.of(s("{\"a\":2147483647,\"b\":2147483648,\"c\":-0,\"d\":1.0,\"e\":1e3}")),
            ok(tableOf(List.of("a", "b", "c", "d", "e"),
                List.of(i(2147483647), n(2147483648.0), i(0), n(1.0), n(1000.0))))));
        seeds.add(new Seed(StdlibFunctionId.JSON_PARSE, List.of(s("{\"a\":}")),
            fail(FailurePolicyId.JSON_PARSE_SYNTAX, DiagnosticCode.E8001,
                "JSON parse error at position 6: "
                    + SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER,
                null, null, "oneBasedByteOffset", "6", "reason",
                SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER)));
        seeds.add(new Seed(StdlibFunctionId.JSON_PARSE, List.of(s("1")), ok(i(1))));

        // ---- json stringify: insertion order, RFC-8259 escaping,
        //      first declaration-order failure ----
        seeds.add(new Seed(StdlibFunctionId.JSON_STRINGIFY,
            List.of(tableOf(List.of("a", "b"), List.of(i(1), i(2)))),
            ok(s("{\"a\":1,\"b\":2}"))));
        seeds.add(new Seed(StdlibFunctionId.JSON_STRINGIFY,
            List.of(tableOf(List.of("a"), List.of(s("x\ny")))),
            ok(s("{\"a\":\"x\\ny\"}"))));
        seeds.add(new Seed(StdlibFunctionId.JSON_STRINGIFY,
            List.of(tableOf(List.of("a"), List.of(s("😀")))),
            ok(s("{\"a\":\"😀\"}"))));
        {
            SemanticTable<Value> table = new SemanticTable<>();
            table.put("a", i(1));
            table.put("f", new Value.Other(ActualKind.FUNCTION, null));
            table.put("b", i(2));
            seeds.add(new Seed(StdlibFunctionId.JSON_STRINGIFY,
                List.of(new Value.Table(table)),
                fail(FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
                    "value at f is not JSON serializable: function", null, null,
                    "fieldPath", "f", "actual", "function")));
        }
        {
            SemanticTable<Value> table = new SemanticTable<>();
            table.put("f", n(Double.NaN));
            seeds.add(new Seed(StdlibFunctionId.JSON_STRINGIFY,
                List.of(new Value.Table(table)),
                fail(FailurePolicyId.JSON_TO_ERROR, DiagnosticCode.E8001,
                    "value at f is not JSON serializable: number", null, null,
                    "fieldPath", "f", "actual", "number")));
        }

        // ---- math ----
        seeds.add(seed(StdlibFunctionId.MATH_FLOOR, List.of(n(1.5)), ok(n(1.0))));
        seeds.add(seed(StdlibFunctionId.MATH_FLOOR, List.of(n(-1.5)), ok(n(-2.0))));
        seeds.add(seed(StdlibFunctionId.MATH_CEIL, List.of(n(1.5)), ok(n(2.0))));
        seeds.add(seed(StdlibFunctionId.MATH_CEIL, List.of(n(-1.5)), ok(n(-1.0))));
        seeds.add(seed(StdlibFunctionId.MATH_SQRT, List.of(n(4.0)), ok(n(2.0))));
        seeds.add(seed(StdlibFunctionId.MATH_SQRT, List.of(n(2.0)), ok(n(Math.sqrt(2.0)))));
        seeds.add(new Seed(StdlibFunctionId.MATH_SQRT, List.of(n(-4.0)),
            fail(FailurePolicyId.SQRT_NEGATIVE, DiagnosticCode.E8001,
                "sqrt of negative number", null, CanonicalJson.numberHex(-4.0))));
        seeds.add(seed(StdlibFunctionId.MATH_SQRT, List.of(n(Double.NaN)),
            ok(n(Double.NaN))));
        seeds.add(seed(StdlibFunctionId.MATH_SQRT, List.of(n(-0.0)), ok(n(-0.0))));
        seeds.add(seed(StdlibFunctionId.MATH_ABS_INT, List.of(i(-3)), ok(i(3))));
        seeds.add(seed(StdlibFunctionId.MATH_ABS_INT, List.of(i(3)), ok(i(3))));
        seeds.add(new Seed(StdlibFunctionId.MATH_ABS_INT, List.of(i(Integer.MIN_VALUE)),
            fail(FailurePolicyId.INT32_RESULT, DiagnosticCode.E8004,
                "int out of range", null, null)));
        seeds.add(seed(StdlibFunctionId.MATH_ABS_NUMBER, List.of(n(-1.5)), ok(n(1.5))));
        seeds.add(seed(StdlibFunctionId.MATH_ABS_NUMBER, List.of(n(-0.0)), ok(n(0.0))));
        seeds.add(seed(StdlibFunctionId.MATH_MIN_INT, List.of(i(2), i(3)), ok(i(2))));
        seeds.add(seed(StdlibFunctionId.MATH_MIN_INT, List.of(i(2), i(2)), ok(i(2))));
        seeds.add(seed(StdlibFunctionId.MATH_MIN_INT, List.of(i(-1), i(-2)), ok(i(-2))));
        seeds.add(seed(StdlibFunctionId.MATH_MAX_INT, List.of(i(2), i(3)), ok(i(3))));
        seeds.add(seed(StdlibFunctionId.MATH_MAX_INT, List.of(i(2), i(2)), ok(i(2))));
        seeds.add(seed(StdlibFunctionId.MATH_MAX_INT, List.of(i(-1), i(-2)), ok(i(-1))));

        return List.copyOf(seeds);
    }

    // =========================================================================
    // Capture sinks
    // =========================================================================

    private static final class CaptureSink implements ConsoleSink {
        final Channel channel;
        final List<byte[]> writes = new ArrayList<>();

        CaptureSink(Channel channel) {
            this.channel = channel;
        }

        @Override
        public Channel channel() {
            return channel;
        }

        @Override
        public void write(byte[] bytes) {
            writes.add(bytes);
        }
    }

    private static final class FailingSink implements ConsoleSink {
        final Channel channel;

        FailingSink(Channel channel) {
            this.channel = channel;
        }

        @Override
        public Channel channel() {
            return channel;
        }

        @Override
        public void write(byte[] bytes) {
            throw new IllegalStateException("infrastructure sink failure");
        }
    }

    // =========================================================================
    // Fault views (each injected break replaces exactly one production seam)
    // =========================================================================

    private interface CatalogView {
        Optional<StdlibFunctionCatalog.Entry> lookup(String modulePath, String exportName);
    }

    private interface ExecutorView {
        Outcome<Value> execute(SemanticOp op, List<Value> args, ConsoleSink sink);
    }

    private interface ProjectionView {
        BoundaryFailure view(BoundaryFailure failure);
    }

    private interface HomeRowsView {
        List<SemanticCapability> homeRows(SemanticOp op);
    }

    /** The TRIM_TAMPER executor: the production executor with U+00A0 added to the trim set. */
    private static Outcome<Value> tamperedExecute(SemanticOp op, List<Value> args,
                                                  ConsoleSink sink) {
        Outcome<Value> outcome = SharedStdlibSemantics.execute(op, args, sink);
        if (op.payload() instanceof KindPayload.StdlibCallPayload payload
                && payload.function() == StdlibFunctionId.STRING_TRIM
                && outcome instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.String string
                && string.scalar() instanceof UnicodeScalars.Valid valid) {
            String carrier = valid.carrier();
            while (carrier.startsWith("\u00a0")) {
                carrier = carrier.substring(1);
            }
            while (carrier.endsWith("\u00a0")) {
                carrier = carrier.substring(0, carrier.length() - 1);
            }
            return new Outcome.Success<>(s(carrier));
        }
        return outcome;
    }

    /** The PROJECTION_TAMPER view: the resolved record with the {@code {reason}} replaced. */
    private static BoundaryFailure tamperedProjection(BoundaryFailure failure) {
        Map<String, String> metadata = new LinkedHashMap<>(failure.metadata());
        metadata.put("reason", "tampered-reason");
        return BoundaryFailure.fromRow(FailureContractRegistry.row(failure.policy()), 0,
            failure.expected(), failure.actual(), metadata, failure.cause());
    }

    // =========================================================================
    // The corpus context one pipeline run shares across its phases
    // =========================================================================

    private record Corpus(CheckedProjectBuildResult checked, LoweredModuleUnit unit,
                          StructuredBodyTable table, LoweredModuleUnit trivialUnit,
                          List<SemanticOp> stdlibOps,
                          Map<StdlibFunctionId, SemanticOp> ops) {
    }

    // =========================================================================
    // The pipeline
    // =========================================================================

    private static PipelineReport runPipeline(Fault fault) {
        // ---- T1: catalog lookup ----
        System.out.println("-- T1: the closed StdlibFunctionCatalog lookup --");
        CatalogView catalog = fault == Fault.CATALOG_DROP
            ? (module, name) -> "std.string".equals(module) && "trim".equals(name)
                ? Optional.empty() : StdlibFunctionCatalog.lookup(module, name)
            : StdlibFunctionCatalog::lookup;
        EnumSet<StdlibFunctionId> covered = EnumSet.noneOf(StdlibFunctionId.class);
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            Optional<StdlibFunctionCatalog.Entry> found =
                catalog.lookup(entry.modulePath(), entry.exportName());
            if (found.isEmpty() || !found.get().equals(entry)) {
                String detail = "T1 StdlibFunctionCatalog — missing catalog entry "
                    + entry.modulePath() + "." + entry.exportName() + " ("
                    + entry.function() + ") — expected the closed row, got absent";
                return fault == Fault.CATALOG_DROP ? injectedFault(detail) : defect(detail);
            }
            covered.add(entry.function());
        }
        if (!covered.equals(EnumSet.allOf(StdlibFunctionId.class))) {
            EnumSet<StdlibFunctionId> missing = EnumSet.allOf(StdlibFunctionId.class);
            missing.removeAll(covered);
            return defect("T1 StdlibFunctionCatalog — the catalog does not cover the "
                + "closed 20-id set — expected every id, got missing " + missing);
        }
        check(catalog.lookup("std.time", "nowMillis").isEmpty(),
            "T1: std/time.nowMillis has no catalog entry (the time lock holds at the "
                + "catalog)");
        check(catalog.lookup("std.string", "unknownMember").isEmpty(),
            "T1: an unknown stdlib member is not a catalog entry");
        check(catalog.lookup("user.module", "length").isEmpty(),
            "T1: a user-module member is never a catalog entry");
        check(catalog.lookup(null, "x").isEmpty()
                && catalog.lookup("std.string", null).isEmpty(),
            "T1: absent inputs are absent entries, never errors");
        check(StdlibFunctionId.RESERVED_NAMES.equals(List.of("TIME_NOW_MILLIS"))
                && StdlibFunctionId.values().length == 20,
            "T1: TIME_NOW_MILLIS stays the single reserved name, outside the closed "
                + "20-value set");

        // ---- T2: recognition + STDLIB_CALL lowering ----
        System.out.println("-- T2: recognition and the STDLIB_CALL lowering arm --");
        Corpus corpus = phaseT2(fault);
        if (corpus == null) {
            String detail = t2FailureDetail;
            return fault == Fault.POLICY_MISSTAMP ? injectedFault(detail) : defect(detail);
        }

        // ---- T3: SharedStdlibSemantics execution ----
        System.out.println("-- T3: SharedStdlibSemantics execution of every id --");
        PipelineReport t3 = phaseT3(fault, corpus);
        if (!t3.ok()) {
            return t3;
        }

        // ---- T4: the exact resolved projections ----
        System.out.println("-- T4: the exact resolved projections --");
        PipelineReport t4 = phaseT4(fault, corpus);
        if (!t4.ok()) {
            return t4;
        }

        // ---- T5: claiming seam, the time lock, and the D3 disposition ----
        System.out.println("-- T5: claiming evidence, the time lock, the D3 disposition --");
        PipelineReport t5 = phaseT5(fault, corpus);
        if (!t5.ok()) {
            return t5;
        }

        return new PipelineReport(true, null);
    }

    /** The T2 failure detail (set by {@link #phaseT2} before returning null). */
    private static String t2FailureDetail = "";

    private static Corpus phaseT2(Fault fault) {
        t2FailureDetail = "";
        Path tmp = null;
        try {
            tmp = Files.createTempDirectory("deal-stdlib-integration-t2");
            CheckedProjectBuildResult checked = compileProject(tmp, corpusSources(),
                "main.deal");
            if (checked == null) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — the corpus project failed "
                    + "the checked-project build";
                return null;
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — the 20-id corpus module "
                    + "failed lowering: " + (lowering == null ? "null"
                        : lowering.diagnostics());
                return null;
            }
            LoweredModuleUnit unit = lowering.unit();
            List<SemanticOp> calls = stdlibOps(unit);
            if (calls.size() != 20) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — expected exactly one "
                    + "STDLIB_CALL per cataloged id (20), got " + calls.size();
                return null;
            }
            EnumSet<StdlibFunctionId> produced = EnumSet.noneOf(StdlibFunctionId.class);
            Map<StdlibFunctionId, SemanticOp> ops = new LinkedHashMap<>();
            for (SemanticOp op : calls) {
                StdlibFunctionId function =
                    ((KindPayload.StdlibCallPayload) op.payload()).function();
                produced.add(function);
                ops.put(function, op);
            }
            if (!produced.equals(EnumSet.allOf(StdlibFunctionId.class))) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — the produced id set "
                    + "expected the closed 20-id set, got " + produced;
                return null;
            }
            for (SemanticOp op : calls) {
                KindPayload.StdlibCallPayload payload =
                    (KindPayload.StdlibCallPayload) op.payload();
                StdlibFunctionId function = payload.function();
                StdlibFunctionCatalog.Entry row = catalogEntryOf(function);
                check(payload.effectCapability() == SemanticCapability.STDLIB_SEMANTICS,
                    "T2: " + function + " carries effectCapability STDLIB_SEMANTICS");
                check(payload.args().equals(op.operands())
                        && payload.args().size() == row.parameterDescriptors().size(),
                    "T2: " + function + " payload args equal the operands in "
                        + "left-to-right order");
                check(op.operandTypes().equals(row.parameterDescriptors()),
                    "T2: " + function + " operandTypes equal the declared parameter "
                        + "descriptors in order");
                check(op.result() instanceof deal.semantic.ir.ValueId
                        && op.resultType().equals(row.returnDescriptor()),
                    "T2: " + function + " publishes one fresh result with the declared "
                        + "return descriptor " + row.returnDescriptor());
                check(op.failurePolicy() == SemanticIrValidator.stdlibPolicy(function),
                    "T2: " + function + " stamps failurePolicy "
                        + SemanticIrValidator.stdlibPolicy(function)
                        + " from the single validator table; got " + op.failurePolicy());
                List<SemanticOp> children = childrenOf(unit, op.opId());
                if (children.size() != row.parameterDescriptors().size() + 1) {
                    t2FailureDetail = "T2 STDLIB_CALL lowering — " + function
                        + " expected " + (row.parameterDescriptors().size() + 1)
                        + " boundary children (" + row.parameterDescriptors().size()
                        + " parameters + 1 return), got " + children.size();
                    return null;
                }
                for (int index = 0; index < children.size(); index++) {
                    SemanticOp child = children.get(index);
                    if (child.kind() != SemanticOpKind.BOUNDARY
                            || !(child.payload() instanceof KindPayload.BoundaryPayload
                                boundary)) {
                        t2FailureDetail = "T2 STDLIB_CALL lowering — " + function
                            + " child " + index + " is not a BOUNDARY op";
                        return null;
                    }
                    if (index < row.parameterDescriptors().size()) {
                        if (boundary.kind() != deal.semantic.ir.BoundaryKind.STDLIB_PARAMETER
                                || !boundary.descriptor().equals(
                                    row.parameterDescriptors().get(index))
                                || !boundary.input().equals(op.operands().get(index))) {
                            t2FailureDetail = "T2 STDLIB_CALL lowering — " + function
                                + " parameter boundary " + index + " expected kind "
                                + "STDLIB_PARAMETER with the declared descriptor and the "
                                + "argument input, got kind=" + boundary.kind()
                                + " descriptor=" + boundary.descriptor();
                            return null;
                        }
                    } else {
                        if (boundary.kind() != deal.semantic.ir.BoundaryKind.STDLIB_RETURN
                                || !boundary.descriptor().equals(row.returnDescriptor())
                                || !boundary.input().equals(op.result())) {
                            t2FailureDetail = "T2 STDLIB_CALL lowering — " + function
                                + " expected the single STDLIB_RETURN boundary with the "
                                + "declared return descriptor and the call result, got "
                                + "kind=" + boundary.kind() + " descriptor="
                                + boundary.descriptor();
                            return null;
                        }
                    }
                    check(child.failurePolicy()
                            == descriptorKindPolicy(boundary.descriptor()),
                        "T2: " + function + " boundary child " + index
                            + " carries the descriptor-kind-rule policy");
                }
            }

            // The unit passes the closed validator on the typed surface.
            Optional<CompilerDiagnostic> validation =
                SemanticIrValidator.validate(unit, factsOf(checked));
            if (validation.isPresent()) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — the corpus unit failed the "
                    + "closed validator: " + validation.get().message();
                return null;
            }

            // The negative: a user-module member call is never recognized
            // and never produces a STDLIB_CALL (the generic call shape).
            SemanticLowerer.LoweringResult plainLowering = lowerSubject(checked, "plain");
            check(plainLowering != null && plainLowering.hasErrors()
                    && plainLowering.unit() == null,
                "T2: the user-module member call fails the common unit with the "
                    + "generic call shape and produces zero STDLIB_CALL ops: "
                    + (plainLowering == null ? "null" : plainLowering.diagnostics()));
            if (plainLowering != null && plainLowering.hasErrors()) {
                check(plainLowering.diagnostics().stream().anyMatch(diagnostic ->
                        diagnostic.message().contains("call callee shape MemberAccessExpr")),
                    "T2: the failure is the generic non-direct call shape, never a "
                        + "stdlib production: " + plainLowering.diagnostics());
            }

            // The claim-negative carrier: a module without any cataloged
            // call lowers cleanly with zero STDLIB_CALL ops.
            SemanticLowerer.LoweringResult trivialLowering = lowerSubject(checked, "trivial");
            check(trivialLowering != null && !trivialLowering.hasErrors()
                    && trivialLowering.unit() != null,
                "T2: the trivial module lowers cleanly: " + (trivialLowering == null
                    ? "null" : trivialLowering.diagnostics()));
            if (trivialLowering == null || trivialLowering.hasErrors()
                    || trivialLowering.unit() == null) {
                t2FailureDetail = "T2 STDLIB_CALL lowering — the trivial claim-negative "
                    + "module failed lowering: " + (trivialLowering == null ? "null"
                        : trivialLowering.diagnostics());
                return null;
            }
            check(stdlibOps(trivialLowering.unit()).isEmpty(),
                "T2: a module without a cataloged call produces zero STDLIB_CALL ops");

            // The injected fault: the STRING_TRIM op stamps the wrong policy.
            if (fault == Fault.POLICY_MISSTAMP) {
                RawUnit raw = RawUnit.fromTyped(unit);
                RawUnit misstamped = transformOps(raw, op ->
                    isStdlibTrim(op) ? withFailurePolicy(op, "INT32_RESULT") : op);
                Optional<CompilerDiagnostic> diag = validateText(misstamped,
                    factsOf(checked));
                if (diag.isEmpty()) {
                    t2FailureDetail = "T2 STDLIB_CALL lowering — STRING_TRIM stamps "
                        + "failurePolicy INT32_RESULT — expected NO_DEAL_FAILURE from "
                        + "the single stdlibPolicy table, got no validation rejection";
                    return null;
                }
                t2FailureDetail = "T2 STDLIB_CALL lowering — STRING_TRIM stamps "
                    + "failurePolicy INT32_RESULT — expected NO_DEAL_FAILURE from the "
                    + "single stdlibPolicy table, got the validation rejection: "
                    + diag.get().message();
                return null;
            }

            return new Corpus(checked, unit, lowering.table(), trivialLowering.unit(),
                calls, ops);
        } catch (Exception e) {
            t2FailureDetail = "T2 STDLIB_CALL lowering threw: " + e;
            return null;
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // Raw-op transforms (the T2 misstamp and the T5 validator negatives)
    // =========================================================================

    private static String payloadString(RawOp op, String key) {
        for (CanonicalJson.Entry entry : op.payload().entries()) {
            if (entry.key().equals(key)
                    && entry.value() instanceof CanonicalJson.Str str) {
                return str.value();
            }
        }
        return null;
    }

    private static boolean isStdlibTrim(RawOp op) {
        return "STDLIB_CALL".equals(op.kind())
            && "STRING_TRIM".equals(payloadString(op, "function"));
    }

    /** One raw op with the failure policy replaced in both the op and the snapshot. */
    private static RawOp withFailurePolicy(RawOp op, String policy) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.snapshot().entries()) {
            entries.add(entry.key().equals("failurePolicy")
                ? CanonicalJson.e(entry.key(), CanonicalJson.str(policy)) : entry);
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(entries);
        String digest = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(snapshot);
        return new RawOp(op.opId(), op.kind(), policy, op.parentOpId(), op.resultValue(),
            op.resultToken(), op.resultType(), op.operands(), op.operandTypes(),
            op.payload(), op.selector(), digest, snapshot);
    }

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

    /** One raw unit with the named capabilities added to its claim set. */
    private static RawUnit withCapabilities(RawUnit raw, String... extra) {
        List<String> capabilities = new ArrayList<>(raw.requiredCapabilities());
        capabilities.addAll(List.of(extra));
        return new RawUnit(raw.modulePath(), raw.semanticProfile(), raw.interfaceHash(),
            raw.loweringContextHash(), capabilities, raw.coverage(), raw.bindings(),
            raw.ops());
    }

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

    /** Serializes one raw unit through the text surface and validates it. */
    private static Optional<CompilerDiagnostic> validateText(RawUnit raw,
            SemanticIrValidator.ComparisonFacts facts) {
        return SemanticIrValidator.validateText(
            ContractSnapshotCanonicalizer.serializeText(
                ContractSnapshotCanonicalizer.toJson(raw)),
            facts);
    }

    // =========================================================================
    // T3: SharedStdlibSemantics execution of every id with the pinned seeds
    // =========================================================================

    private static PipelineReport phaseT3(Fault fault, Corpus corpus) {
        ExecutorView executor = fault == Fault.TRIM_TAMPER
            ? StdlibIntegrationTest::tamperedExecute
            : SharedStdlibSemantics::execute;
        CaptureSink stdout = new CaptureSink(Channel.STDOUT);
        CaptureSink stderr = new CaptureSink(Channel.STDERR);
        for (Seed seed : seeds()) {
            SemanticOp op = corpus.ops().get(seed.function());
            if (op == null) {
                return defect("T3 SharedStdlibSemantics — " + seed.function()
                    + " has no lowered STDLIB_CALL op (the T2 production is broken)");
            }
            ConsoleSink sink = switch (seed.function()) {
                case CONSOLE_LOG -> stdout;
                case CONSOLE_ERROR -> stderr;
                default -> null;
            };
            Outcome<Value> outcome = executor.execute(op, seed.args(), sink);
            if (!pinnedMatches(outcome, seed.outcome(), op.origin())) {
                String detail = "T3 SharedStdlibSemantics — " + seed.function()
                    + " — expected " + describePinned(seed.outcome()) + ", got "
                    + describeOutcome(outcome);
                return fault == Fault.TRIM_TAMPER
                        && seed.function() == StdlibFunctionId.STRING_TRIM
                    ? injectedFault(detail) : defect(detail);
            }
        }
        check(stdout.writes.size() == 2
                && Arrays.equals(stdout.writes.get(0), new byte[] {'\n'})
                && Arrays.equals(stdout.writes.get(1),
                    "héllo 😀\n".getBytes(StandardCharsets.UTF_8)),
            "T3: the two console.log executions emitted exactly one ordered STDOUT "
                + "effect each — the exact scalar UTF-8 bytes plus one '\\n'");
        check(stderr.writes.size() == 1
                && Arrays.equals(stderr.writes.get(0),
                    "err\n".getBytes(StandardCharsets.UTF_8)),
            "T3: console.error emitted exactly one STDERR effect 'err\\n'");
        for (Seed seed : seeds()) {
            if (seed.function() == StdlibFunctionId.CONSOLE_LOG
                    || seed.function() == StdlibFunctionId.CONSOLE_ERROR) {
                check(seed.outcome() instanceof Pinned.PinnedSuccess(Value.Null ignored),
                    "T3: " + seed.function() + " returns the null value");
            }
        }
        try {
            executor.execute(corpus.ops().get(StdlibFunctionId.CONSOLE_LOG),
                List.of(s("x")), new FailingSink(Channel.STDOUT));
            return defect("T3 SharedStdlibSemantics — a failing sink must propagate "
                + "as infrastructure (INFRASTRUCTURE_ONLY), got a silent success");
        } catch (IllegalStateException expected) {
            check(true, "T3: the sink failure propagates uncaught — infrastructure "
                + "failure, never a DEAL error");
        }

        // The end-to-end oracle drive: the validated unit executes through
        // the production executor with the exact effects and terminal.
        SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(corpus.unit(),
            corpus.table());
        check(run.terminal() instanceof SemanticRuntimeModel.Terminal.Success success
                && "null".equals(success.resultAtom()),
            "T3: the corpus unit executes through the semantic oracle to the null "
                + "terminal; got " + run.terminal());
        List<SemanticRuntimeModel.EffectEvent> effects = run.effects();
        check(effects.size() == 2
                && effects.get(0).kind() == SemanticRuntimeModel.EffectEvent.Kind.CONSOLE_WRITE
                && effects.get(0).text().equals("log")
                && effects.get(1).kind() == SemanticRuntimeModel.EffectEvent.Kind.CONSOLE_WRITE
                && effects.get(1).text().equals("error"),
            "T3: the oracle recorded exactly the two ordered console effects in "
                + "source order; got " + effects);
        return new PipelineReport(true, null);
    }

    // =========================================================================
    // T4: the exact resolved projections
    // =========================================================================

    private static PipelineReport phaseT4(Fault fault, Corpus corpus) {
        ProjectionView view = fault == Fault.PROJECTION_TAMPER
            ? StdlibIntegrationTest::tamperedProjection : failure -> failure;
        SemanticOp parseOp = corpus.ops().get(StdlibFunctionId.JSON_PARSE);

        // (a) JSON_PARSE_SYNTAX: the exact template, both metadata keys,
        // the call origin, no cause — cross-checked against the registry row.
        Outcome<Value> outcome = SharedStdlibSemantics.execute(parseOp,
            List.of(s("{\"a\":}")), null);
        if (!(outcome instanceof Outcome.Failure<Value> failure)) {
            return defect("T4 failure projection — JSON_PARSE_SYNTAX expected a "
                + "failure for '{\\\"a\\\":}', got " + describeOutcome(outcome));
        }
        BoundaryFailure projection = view.view(failure.failure().failure());
        FailurePolicyRow row = FailureContractRegistry.row(FailurePolicyId.JSON_PARSE_SYNTAX);
        Map<String, String> pinnedMetadata = Map.of("oneBasedByteOffset", "6", "reason",
            SharedStdlibSemantics.REASON_UNEXPECTED_CHARACTER);
        String expectedMessage = BoundaryFailure.fromRow(row, 0, null, null,
            pinnedMetadata, null).message();
        if (projection.policy() != FailurePolicyId.JSON_PARSE_SYNTAX
                || projection.code() != DiagnosticCode.E8001
                || !projection.message().equals(expectedMessage)
                || !projection.metadata().equals(pinnedMetadata)
                || projection.cause() != null
                || !failure.failure().origin().equals(parseOp.origin())) {
            String detail = "T4 failure projection — JSON_PARSE_SYNTAX — expected "
                + "policy JSON_PARSE_SYNTAX, E8001 '" + expectedMessage + "' with "
                + "metadata " + pinnedMetadata + ", the call origin and no cause; got "
                + "policy=" + projection.policy() + " code=" + projection.code()
                + " message='" + projection.message() + "' metadata="
                + projection.metadata() + " cause=" + projection.cause()
                + " origin=" + failure.failure().origin();
            return fault == Fault.PROJECTION_TAMPER
                ? injectedFault(detail) : defect(detail);
        }
        check(row.templates().contains(
                "JSON parse error at position {oneBasedByteOffset}: {reason}")
                && row.metadataKeys().equals(List.of("oneBasedByteOffset", "reason")),
            "T4: the registry row carries the exact template and the two metadata keys");

        // (b) A successful parse whose top-level value is not a table
        // fails the STDLIB_RETURN boundary (the descriptor-kind rule).
        Outcome<Value> scalar = SharedStdlibSemantics.execute(parseOp, List.of(s("1")),
            null);
        check(scalar instanceof Outcome.Success<Value> success
                && success.value() instanceof Value.Int intValue
                && intValue.value() == 1,
            "T4: the parse of the top-level scalar '1' succeeds in the algorithm "
                + "(the return boundary fails next); got " + describeOutcome(scalar));
        BoundaryOutcome returnCheck = BoundaryExecutor.check(
            descriptorKindPolicy(DESC_TABLE), DESC_TABLE,
            BoundaryValueView.ofInt(1), BoundaryContext.none());
        check(returnCheck instanceof BoundaryOutcome.Fail fail
                && fail.failure().code() == DiagnosticCode.E8001
                && fail.failure().message().equals("expected table, got int")
                && fail.failure().policy() == FailurePolicyId.TYPE_DESCRIPTOR,
            "T4: the STDLIB_RETURN boundary rejects the non-table top-level parse "
                + "with E8001 'expected table, got int'");

        // (c) JSON_TO_ERROR: the first declaration-order failure with {fieldPath}/{actual}.
        SemanticOp stringifyOp = corpus.ops().get(StdlibFunctionId.JSON_STRINGIFY);
        SemanticTable<Value> table = new SemanticTable<>();
        table.put("a", i(1));
        table.put("f", new Value.Other(ActualKind.FUNCTION, null));
        table.put("b", i(2));
        Outcome<Value> stringify = SharedStdlibSemantics.execute(stringifyOp,
            List.of(new Value.Table(table)), null);
        if (!(stringify instanceof Outcome.Failure<Value> stringifyFailure)) {
            return defect("T4 failure projection — JSON_TO_ERROR expected a failure for "
                + "the function leaf, got " + describeOutcome(stringify));
        }
        BoundaryFailure toError = view.view(stringifyFailure.failure().failure());
        if (toError.policy() != FailurePolicyId.JSON_TO_ERROR
                || toError.code() != DiagnosticCode.E8001
                || !toError.message()
                    .equals("value at f is not JSON serializable: function")
                || !toError.metadata()
                    .equals(Map.of("fieldPath", "f", "actual", "function"))
                || toError.cause() != null
                || !stringifyFailure.failure().origin().equals(stringifyOp.origin())) {
            return defect("T4 failure projection — JSON_TO_ERROR — expected E8001 "
                + "'value at f is not JSON serializable: function' with "
                + "{fieldPath:f, actual:function} at the call origin and no cause; got "
                + "policy=" + toError.policy() + " code=" + toError.code()
                + " message='" + toError.message() + "' metadata=" + toError.metadata());
        }

        // (d) SQRT_NEGATIVE and INT32_RESULT project exactly.
        SemanticOp sqrtOp = corpus.ops().get(StdlibFunctionId.MATH_SQRT);
        Outcome<Value> sqrt = SharedStdlibSemantics.execute(sqrtOp, List.of(n(-4.0)),
            null);
        check(sqrt instanceof Outcome.Failure<Value> sqrtFailure
                && sqrtFailure.failure().failure().policy()
                    == FailurePolicyId.SQRT_NEGATIVE
                && sqrtFailure.failure().failure().code() == DiagnosticCode.E8001
                && sqrtFailure.failure().failure().message()
                    .equals("sqrt of negative number")
                && CanonicalJson.numberHex(-4.0)
                    .equals(sqrtFailure.failure().failure().actual())
                && sqrtFailure.failure().origin().equals(sqrtOp.origin()),
            "T4: SQRT_NEGATIVE projects exactly — E8001 'sqrt of negative number' at "
                + "the call origin with the canonical hex-float actual");
        SemanticOp absOp = corpus.ops().get(StdlibFunctionId.MATH_ABS_INT);
        Outcome<Value> abs = SharedStdlibSemantics.execute(absOp,
            List.of(i(Integer.MIN_VALUE)), null);
        check(abs instanceof Outcome.Failure<Value> absFailure
                && absFailure.failure().failure().policy()
                    == FailurePolicyId.INT32_RESULT
                && absFailure.failure().failure().code() == DiagnosticCode.E8004
                && absFailure.failure().failure().message().equals("int out of range")
                && absFailure.failure().failure().metadata().isEmpty()
                && absFailure.failure().origin().equals(absOp.origin()),
            "T4: INT32_RESULT projects exactly — absInt(-2147483648) is E8004 "
                + "'int out of range' at the call origin");

        // (e) The boundary precedence: invalid scalar encodings fail the
        // argument's STDLIB_PARAMETER boundary before any algorithm runs.
        BoundaryOutcome invalidCheck = BoundaryExecutor.check(
            FailurePolicyId.TYPE_DESCRIPTOR, DESC_STRING,
            BoundaryValueView.of(ActualKind.INVALID_UNICODE), BoundaryContext.none());
        check(invalidCheck instanceof BoundaryOutcome.Fail invalidFail
                && invalidFail.failure().code() == DiagnosticCode.E8001
                && invalidFail.failure().message()
                    .equals("expected string, got invalid Unicode scalar encoding"),
            "T4: an invalid scalar encoding is rejected at the argument's "
                + "STDLIB_PARAMETER boundary with the exact E8001 before any "
                + "algorithm runs");

        // (f) The end-to-end oracle projections: the non-table top-level
        // parse fails the STDLIB_RETURN boundary, and the syntax defect
        // fails with the exact JSON_PARSE_SYNTAX projection at the call
        // origin.
        Scenario nonTable = lowerScenario("""
            import * as json from "std/json"

            function run(): null {
              let t: table = json.parse("1")
              return null
            }

            function main(): null {
              run()
              return null
            }
            """, "the non-table top-level scenario");
        if (nonTable != null) {
            SemanticOp call = stdlibOpBy(nonTable.unit(), StdlibFunctionId.JSON_PARSE);
            SemanticOp returnBoundary = stdlibReturnBoundaryOf(nonTable.unit(), call);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(nonTable.unit(),
                nonTable.table());
            if (run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure terminal) {
                check(terminal.error().code().equals("E8001")
                        && terminal.error().message().equals("expected table, got int")
                        && terminal.error().cause() == null
                        && returnBoundary != null
                        && terminal.error().origin().equals(originAtomOf(returnBoundary)),
                    "T4: the oracle terminal of the non-table top-level parse is the "
                        + "exact STDLIB_RETURN failure at the return-boundary origin: "
                        + terminal.error());
            } else {
                fail("T4: the non-table scenario expected a DealFailure terminal, got "
                    + run.terminal());
            }
            deleteRecursively(nonTable.tmp());
        }
        Scenario syntax = lowerScenario("""
            import * as json from "std/json"

            function run(): null {
              let t: table = json.parse("x")
              return null
            }

            function main(): null {
              run()
              return null
            }
            """, "the syntax-defect scenario");
        if (syntax != null) {
            SemanticOp call = stdlibOpBy(syntax.unit(), StdlibFunctionId.JSON_PARSE);
            SemanticRuntimeModel.ConsumerRun run = SemanticOracle.execute(syntax.unit(),
                syntax.table());
            if (run.terminal()
                    instanceof SemanticRuntimeModel.Terminal.DealFailure terminal) {
                check(terminal.error().code().equals("E8001")
                        && terminal.error().message().equals(
                            "JSON parse error at position 1: unexpected character")
                        && terminal.error().cause() == null
                        && call != null
                        && terminal.error().origin().equals(originAtomOf(call)),
                    "T4: the oracle terminal of the syntax defect is the exact "
                        + "JSON_PARSE_SYNTAX projection at the call origin with no "
                        + "cause: " + terminal.error());
            } else {
                fail("T4: the syntax scenario expected a DealFailure terminal, got "
                    + run.terminal());
            }
            deleteRecursively(syntax.tmp());
        }
        return new PipelineReport(true, null);
    }

    /** The single {@code STDLIB_CALL} carrying the given id, or null. */
    private static SemanticOp stdlibOpBy(LoweredModuleUnit unit, StdlibFunctionId function) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL
                    && ((KindPayload.StdlibCallPayload) op.payload()).function() == function) {
                return op;
            }
        }
        return null;
    }

    /** The STDLIB_RETURN child boundary of the call, or null. */
    private static SemanticOp stdlibReturnBoundaryOf(LoweredModuleUnit unit, SemanticOp call) {
        if (call == null) {
            return null;
        }
        for (SemanticOp op : childrenOf(unit, call.opId())) {
            if (op.kind() == SemanticOpKind.BOUNDARY
                    && op.payload() instanceof KindPayload.BoundaryPayload boundary
                    && boundary.kind() == deal.semantic.ir.BoundaryKind.STDLIB_RETURN) {
                return op;
            }
        }
        return null;
    }

    /** One lowered-and-validated scenario unit. */
    private record Scenario(LoweredModuleUnit unit, StructuredBodyTable table,
                            CheckedProjectBuildResult checked, Path tmp) {
    }

    /** Compiles + lowers one stdlib scenario in the two-module carrier shape. */
    private static Scenario lowerScenario(String libSource, String what) {
        try {
            Path tmp = Files.createTempDirectory("deal-stdlib-integration-t4");
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
            CheckedModuleInput subject = moduleOf(checked.input(), "lib");
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
            check(manifest.capabilities().contains(SemanticCapability.STDLIB_SEMANTICS),
                what + ": the same module's manifest claims STDLIB_SEMANTICS (the "
                    + "plan-time arm over the produced STDLIB_CALL): "
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
            return new Scenario(lowering.unit(), lowering.table(), checked, tmp);
        } catch (Exception e) {
            fail(what + ": scenario setup threw: " + e);
            return null;
        }
    }

    // =========================================================================
    // T5: claiming evidence, the time lock, and the D3 disposition
    // =========================================================================

    private static PipelineReport phaseT5(Fault fault, Corpus corpus) {
        HomeRowsView view = fault == Fault.HOME_ROW_DROP
            ? op -> List.of() : ContainerClaimingSeam::homeRows;
        for (SemanticOp op : corpus.stdlibOps()) {
            List<SemanticCapability> rows = view.homeRows(op);
            if (!rows.equals(List.of(SemanticCapability.STDLIB_SEMANTICS))) {
                String detail = "T5 claiming seam — the STDLIB_CALL → STDLIB_SEMANTICS "
                    + "home row is missing — expected [STDLIB_SEMANTICS], got " + rows;
                return fault == Fault.HOME_ROW_DROP
                    ? injectedFault(detail) : defect(detail);
            }
        }
        for (SemanticOp op : corpus.unit().ops()) {
            if (op.kind() != SemanticOpKind.STDLIB_CALL) {
                check(!ContainerClaimingSeam.homeRows(op)
                        .contains(SemanticCapability.STDLIB_SEMANTICS),
                    "T5: no non-stdlib op homes to STDLIB_SEMANTICS (" + op.kind()
                        + ")");
            }
        }
        check(ContainerClaimingSeam.fullyEvidenced(corpus.unit().ops(),
                SemanticCapability.STDLIB_SEMANTICS),
            "T5: the produced STDLIB_CALL ops fully evidence STDLIB_SEMANTICS → "
                + "{STDLIB_CALL}");
        Set<SemanticCapability> augmented =
            EnumSet.copyOf(ContainerClaimingSeam.E6_GATE_ACTIVATION);
        augmented.add(SemanticCapability.STDLIB_SEMANTICS);
        check(ContainerClaimingSeam.deriveClaims(corpus.unit().ops(), augmented)
                .contains(SemanticCapability.STDLIB_SEMANTICS),
            "T5: with the row active the full-evidence derivation claims "
                + "STDLIB_SEMANTICS from the produced STDLIB_CALL ops");

        // The plan-time manifest arm: the corpus module claims
        // STDLIB_SEMANTICS; the claim-negative module claims nothing.
        RequirementManifestResult manifests = manifestsOf(corpus.checked(), invocation());
        if (manifests == null || manifests.hasErrors()) {
            return defect("T5 claiming seam — the manifest computation failed: "
                + (manifests == null ? "null" : manifests.diagnostics()));
        }
        SemanticRequirementManifest lib = manifestOf(manifests,
            moduleOf(corpus.checked().input(), "lib").moduleId());
        check(lib != null && lib.capabilities().contains(SemanticCapability.STDLIB_SEMANTICS),
            "T5: the corpus module claims STDLIB_SEMANTICS at plan time: "
                + (lib == null ? "no manifest" : lib.capabilities()));
        SemanticRequirementManifest trivial = manifestOf(manifests,
            moduleOf(corpus.checked().input(), "trivial").moduleId());
        check(trivial != null
                && !trivial.capabilities().contains(SemanticCapability.STDLIB_SEMANTICS),
            "T5: a module without a cataloged call claims no STDLIB_SEMANTICS: "
                + (trivial == null ? "no manifest" : trivial.capabilities()));

        try {
            testClaimAndReservedNameNegatives(corpus);
            testTimeLockRouteRefusal();
            testValueReadDisposition();
            testRetainedTimePins();
        } catch (Exception e) {
            fail("T5: a negative drive threw: " + e);
        }
        return new PipelineReport(true, null);
    }

    /** The R-CAPABILITY and reserved-name negatives over the raw text surface. */
    private static void testClaimAndReservedNameNegatives(Corpus corpus) {
        System.out.println("-- T5a: R-CAPABILITY and reserved-name negatives --");
        try {
            RawUnit trivialRaw = RawUnit.fromTyped(corpus.trivialUnit());
            SemanticIrValidator.ComparisonFacts facts = factsOf(corpus.checked());

            Optional<CompilerDiagnostic> semanticsClaim = validateText(
                withCapabilities(trivialRaw, "STDLIB_SEMANTICS"), facts);
            check(semanticsClaim.isPresent()
                    && semanticsClaim.get().message().contains("R-CAPABILITY")
                    && semanticsClaim.get().message().contains("STDLIB_SEMANTICS")
                    && semanticsClaim.get().message().contains("STDLIB_CALL"),
                "T5a: a STDLIB_SEMANTICS claim without a produced STDLIB_CALL fails "
                    + "R-CAPABILITY naming the missing required operation: "
                    + (semanticsClaim.isPresent() ? semanticsClaim.get().message()
                        : "no rejection"));

            Optional<CompilerDiagnostic> conflictClaim = validateText(
                withCapabilities(trivialRaw, "STDLIB_TIME_CONFLICT"), facts);
            check(conflictClaim.isPresent()
                    && conflictClaim.get().message().contains("R-CAPABILITY")
                    && conflictClaim.get().message().contains("STDLIB_TIME_CONFLICT"),
                "T5a: a STDLIB_TIME_CONFLICT claim fails R-CAPABILITY (the empty "
                    + "evidence set is unsatisfiable): "
                    + (conflictClaim.isPresent() ? conflictClaim.get().message()
                        : "no rejection"));

            Optional<CompilerDiagnostic> reservedCapability = validateText(
                withCapabilities(trivialRaw, "TIME_NOW_MILLIS"), facts);
            check(reservedCapability.isPresent()
                    && reservedCapability.get().message().contains("TIME_NOW_MILLIS")
                    && reservedCapability.get().message()
                        .contains("SemanticCapability"),
                "T5a: a capability claim naming TIME_NOW_MILLIS fails in the closed "
                    + "SemanticCapability position: "
                    + (reservedCapability.isPresent() ? reservedCapability.get().message()
                        : "no rejection"));

            RawUnit corpusRaw = RawUnit.fromTyped(corpus.unit());
            Optional<CompilerDiagnostic> untouched = validateText(corpusRaw, facts);
            check(untouched.isEmpty(),
                "T5a: the untouched corpus unit passes the text surface"
                    + (untouched.isPresent() ? ": " + untouched.get().message() : ""));

            RawUnit selectorNegative = transformOps(corpusRaw, op ->
                "STDLIB_CALL".equals(op.kind())
                    ? withSnapshotField(op, "selector", "TIME_NOW_MILLIS") : op);
            Optional<CompilerDiagnostic> selectorFailure =
                validateText(selectorNegative, facts);
            check(selectorFailure.isPresent()
                    && selectorFailure.get().message().contains("R-RESERVED-NAME")
                    && selectorFailure.get().message().contains("TIME_NOW_MILLIS"),
                "T5a: TIME_NOW_MILLIS in the STDLIB_CALL selector position fails "
                    + "R-RESERVED-NAME: "
                    + (selectorFailure.isPresent() ? selectorFailure.get().message()
                        : "no rejection"));

            RawUnit functionNegative = transformOps(corpusRaw, op ->
                "STDLIB_CALL".equals(op.kind())
                    ? withPayloadField(op, "function", "TIME_NOW_MILLIS") : op);
            Optional<CompilerDiagnostic> functionFailure =
                validateText(functionNegative, facts);
            check(functionFailure.isPresent()
                    && functionFailure.get().message().contains("R-RESERVED-NAME")
                    && functionFailure.get().message().contains("TIME_NOW_MILLIS"),
                "T5a: TIME_NOW_MILLIS in the StdlibFunctionId position fails "
                    + "R-RESERVED-NAME: "
                    + (functionFailure.isPresent() ? functionFailure.get().message()
                        : "no rejection"));
        } catch (Exception e) {
            fail("T5a: the claim/reserved-name negatives threw: " + e);
        }
    }

    /** The time lock: STDLIB_TIME_CONFLICT routes LEGACY in every purpose. */
    private static void testTimeLockRouteRefusal() throws java.io.IOException {
        System.out.println("-- T5b: the time lock — STDLIB_TIME_CONFLICT never common-lowerable --");
        Path tmp = Files.createTempDirectory("deal-stdlib-integration-timeroute");
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
            RequirementManifestResult manifests = manifestsOf(checked, invocation());
            if (manifests == null || manifests.hasErrors()) {
                return;
            }
            SemanticRequirementManifest libManifest = manifestOf(manifests, libId);
            SemanticRequirementManifest mainManifest = manifestOf(manifests, mainId);
            check(libManifest != null && libManifest.capabilities().contains(
                    SemanticCapability.STDLIB_TIME_CONFLICT),
                "T5b: the std/time.nowMillis module claims STDLIB_TIME_CONFLICT: "
                    + (libManifest == null ? "no manifest" : libManifest.capabilities()));
            check(mainManifest != null && mainManifest.capabilities().contains(
                    SemanticCapability.STDLIB_TIME_CONFLICT),
                "T5b: the importer claims STDLIB_TIME_CONFLICT by propagation");
            check(libManifest != null && !libManifest.capabilities().contains(
                    SemanticCapability.STDLIB_SEMANTICS),
                "T5b: the time module claims no STDLIB_SEMANTICS (std/time has no "
                    + "catalog entry)");
            for (Object[] purpose : List.<Object[]>of(
                    new Object[] {publicPreActivation(), "PUBLIC_BUILD+PRE_ACTIVATION"},
                    new Object[] {publicV12Active(CapabilityRegistry.releaseRegistry()),
                        "PUBLIC_BUILD+V1_2_ACTIVE"},
                    new Object[] {invocation(), "COMMON_SHADOW"},
                    new Object[] {legacyRegression(), "LEGACY_REGRESSION"})) {
                CompilerInvocation planInvocation = (CompilerInvocation) purpose[0];
                String what = (String) purpose[1];
                Set<ModuleId> requests =
                    planInvocation.purpose().name().equals("COMMON_SHADOW")
                        ? Set.of(libId) : Set.of();
                RoutePlanResult planned = MigrationPlanner.planRoutes(planInvocation,
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, requests);
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY
                        && planned.plan().entries().get(mainId) == ModuleRoute.LEGACY
                        && !planned.plan().shadowModules().contains(libId),
                    what + ": rule 2 keeps the time module and its importer LEGACY — "
                        + "never a shadow module, never common-lowerable: "
                        + (planned == null ? "null" : planned.diagnostics()));
            }
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && lowering.hasErrors() && lowering.unit() == null,
                "T5b: the forced lowering of the time module produces no unit (E6005)");
            if (lowering != null && lowering.hasErrors()) {
                check(lowering.diagnostics().stream().anyMatch(diagnostic ->
                        diagnostic.message().contains("module 'lib'")
                            && diagnostic.message().contains("CONSTRUCT_UNLOWERED")),
                    "T5b: the failure is the exact E6005 with module lib and "
                        + "validatorRule CONSTRUCT_UNLOWERED: " + lowering.diagnostics());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** The D3 disposition: the stdlib-export value read claims nothing, routes by rules 1/3/4/5. */
    private static void testValueReadDisposition() throws java.io.IOException {
        System.out.println("-- T5c: the stdlib-export value-read disposition (D3) --");
        Path tmp = Files.createTempDirectory("deal-stdlib-integration-valueread");
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
                        SemanticCapability.STDLIB_SEMANTICS)
                    && !libManifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "T5c: the value read claims no stdlib capability from the read: "
                    + (libManifest == null ? "no manifest" : libManifest.capabilities()));

            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(legacyRegression(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                    "T5c: rule 1 routes the value-read module LEGACY on the legacy "
                        + "profile (zero diagnostics)");
            }
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(publicPreActivation(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY
                        && planned.plan().entries().get(mainId) == ModuleRoute.LEGACY,
                    "T5c: rule 3 keeps the PRE_ACTIVATION public build LEGACY — the "
                        + "read adds no route rule");
            }
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(invocation(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of(libId));
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.SHARED
                        && planned.plan().shadowModules().contains(libId),
                    "T5c: rule 5 records the value-read module as a shadow SHARED "
                        + "entry under the explicit shadow request");
                SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
                check(lowering != null && lowering.hasErrors() && lowering.unit() == null,
                    "T5c: the common unit containing the read fails with E6005 "
                        + "(no unit, no within-run fallback)");
                if (lowering != null && lowering.hasErrors()) {
                    check(lowering.diagnostics().stream().anyMatch(diagnostic ->
                            diagnostic.message().contains("module 'lib'")
                                && diagnostic.message().contains("CONSTRUCT_UNLOWERED")
                                && diagnostic.message().contains(
                                    "module member access 'console.log'")),
                        "T5c: the exact E6005 names module lib, validatorRule "
                            + "CONSTRUCT_UNLOWERED, and the read position: "
                            + lowering.diagnostics());
                }
            }
            {
                CapabilityRegistry promoted = CapabilityRegistry.releaseRegistry()
                    .withState(SemanticCapability.FOUNDATION_VALUES, Target.LUAJIT,
                        CapabilityRegistry.State.PROMOTED);
                CompilerInvocation activePromoted = publicV12Active(promoted);
                RoutePlanResult planned = MigrationPlanner.planRoutes(activePromoted,
                    promoted, checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of());
                check(planned != null && !planned.hasErrors() && planned.plan() != null
                        && planned.plan().entries().get(libId) == ModuleRoute.LEGACY,
                    "T5c: rule 4 routes the value-read module LEGACY on the promoted "
                        + "profile (the ISSUE-0239 MODULES import arm — the parent "
                        + "verification-3 plan-time reroute, never E6005): "
                        + (planned == null ? "null" : planned.diagnostics()));
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** The retained-time implementation stays unchanged and green. */
    private static void testRetainedTimePins() {
        System.out.println("-- T5d: retained-time implementation --");
        try {
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
                "T5d: std/time.lua is unchanged (byte-identical to the pinned "
                    + "retained content — no time algorithm lands here)");
        } catch (Exception e) {
            fail("T5d: the retained-time pins threw: " + e);
        }
    }

    // =========================================================================
    // The fault-variant expectations and the main
    // =========================================================================

    private static void expectFault(Fault fault, String constituent, String id) {
        PipelineReport report = runPipeline(fault);
        System.out.println("  [fault " + fault + "] " + report.firstFailure());
        check(!report.ok(), fault + " flips the pipeline to failure — the task fails "
            + "if any constituent is broken");
        check(report.firstFailure() != null
                && report.firstFailure().startsWith(constituent),
            fault + " names the first failing constituent " + constituent + ": "
                + report.firstFailure());
        if (report.firstFailure() != null) {
            check(report.firstFailure().contains(id),
                fault + " names the broken stdlib id " + id + ": "
                    + report.firstFailure());
            check(report.firstFailure().contains("expected")
                    && report.firstFailure().contains("got"),
                fault + " reports the exact expected-versus-actual mismatch: "
                    + report.firstFailure());
        }
    }

    public static void main(String[] args) {
        System.out.println("=== Stdlib Integration Verification (ISSUE-0499, "
            + "decomposition tail) ===");

        PipelineReport clean = runPipeline(Fault.NONE);
        check(clean.ok(), "the clean pipeline drives T1–T5 end-to-end through the "
            + "production seams; first failure: " + clean.firstFailure());

        // The all-constituents contract: each injected break flips the
        // task to failure with the broken constituent named.
        expectFault(Fault.CATALOG_DROP, "T1 StdlibFunctionCatalog", "STRING_TRIM");
        expectFault(Fault.POLICY_MISSTAMP, "T2 STDLIB_CALL lowering", "STRING_TRIM");
        expectFault(Fault.TRIM_TAMPER, "T3 SharedStdlibSemantics", "STRING_TRIM");
        expectFault(Fault.PROJECTION_TAMPER, "T4 failure projection", "JSON_PARSE_SYNTAX");
        expectFault(Fault.HOME_ROW_DROP, "T5 claiming seam", "STDLIB_CALL");

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
