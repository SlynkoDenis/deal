package deal.test;

import deal.ast.CallExpr;
import deal.ast.ExportDeclaration;
import deal.ast.FunctionDeclaration;
import deal.ast.MemberAccessExpr;
import deal.ast.StatementNode;
import deal.ast.VariableDeclaration;
import deal.checker.SymbolTable;
import deal.codegen.Backend;
import deal.diagnostics.CompilerDiagnostic;
import deal.module.CompilationOrchestrator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.DescriptorService;
import deal.semantic.LoweringSupport;
import deal.semantic.ModuleRoute;
import deal.semantic.MigrationPlanner;
import deal.semantic.RequirementManifestResult;
import deal.semantic.RoutePlanResult;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.StdlibCallRecognition;
import deal.semantic.StdlibFunctionCatalog;
import deal.semantic.Target;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RawOp;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.ValueId;
import deal.types.Type;

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
 * The ISSUE-0494 {@code STDLIB_CALL} lowering battery: the carrier
 * slice's stdlib branch lowers every recognized cataloged call to exactly
 * one validated {@code STDLIB_CALL} op with left-to-right ordered
 * operands, one {@code STDLIB_PARAMETER} boundary child per declared
 * parameter in one-based order, the single {@code STDLIB_RETURN} boundary
 * run by the call op, descriptor-kind-rule boundary policies, and the op
 * {@code failurePolicy} stamped from the single closed
 * {@link SemanticIrValidator#stdlibPolicy} table
 * ({@code stdlib-operations-and-time-lock} D2, Verification 4).
 *
 * <p>Tests:
 * <ol>
 *   <li>Single-source policy table: {@link SemanticIrValidator#stdlibPolicy}
 *       equals the pinned 21-id mapping exactly; the closed catalog
 *       carries the K7 {@code std.time}/{@code nowMillis} row and
 *       {@code StdlibFunctionId.RESERVED_NAMES} is empty.</li>
 *   <li>The all-id lowering battery: one checked module calling every
 *       cataloged export (the K7 {@code time.nowMillis()} call included)
 *       lowers to exactly one validated
 *       {@code STDLIB_CALL} per call with the declared operand/result
 *       descriptors, the ordered {@code args} payload with
 *       {@code effectCapability = STDLIB_SEMANTICS}, the boundary-child
 *       shape, and the stamped policy read from the single table (fails
 *       if the catalog misses or adds an entry).</li>
 *   <li>Argument operand completion: a call with three side-effecting
 *       argument expressions asserts left-to-right operand production
 *       before the {@code STDLIB_CALL} START.</li>
 *   <li>Negatives: a user-module member call produces no
 *       {@code STDLIB_CALL}.</li>
 *   <li>The stdlib-export value read (ISSUE-0659): the read and its
 *       typed-binding invocation lower and validate through the
 *       call-machine entry — exactly one {@code EXPORT_READ} of the
 *       cataloged export carrying the row's declared descriptor and
 *       exactly one {@code HostFunction} registration keyed by the
 *       read's result identity, plus the {@code CALL(INDIRECT)} the
 *       landed call machine builds over the host cell family; the read
 *       claims no capability.</li>
 *   <li>Validator conformance: a hand-modified wrong stamped policy on a
 *       {@code STDLIB_CALL} fails validation through the text surface
 *       (R-POLICY-KIND); the unmodified unit passes both surfaces.</li>
 *   <li>Dump determinism: repeated dumps and re-lowering are
 *       byte-identical and carry the stdlib payload fields; the dump
 *       re-validates through the text surface.</li>
 *   <li>The K7 time slice: a {@code std/time} member call is recognized
 *       through the closed catalog row and lowers to
 *       {@code STDLIB_CALL(TIME_NOW_MILLIS)} with zero parameter
 *       boundaries, one {@code STDLIB_RETURN} on the declared {@code int},
 *       and the {@code INT32_RESULT} terminal; the module's manifest
 *       claims {@code STDLIB_SEMANTICS} (never
 *       {@code STDLIB_TIME_CONFLICT}) and records the
 *       {@code STDLIB_TIME_NOW_MILLIS} coverage row.</li>
 * </ol>
 */
public class StdlibCallLoweringTest {

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

    /** The fixed common-shadow invocation of the carrier tests. */
    private static CompilerInvocation invocation() {
        return CompilerProfileProvider.resolveCommonShadow(SemanticProfile.DEAL_V1_2_INT32,
            ReleaseState.V1_2_ACTIVE, CapabilityRegistry.releaseRegistry());
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
     * carrier (manifests → full-program lowerer → validator/chain
     * protocol/control-flow validator). The outcome is asserted by the
     * caller: positive batteries require a validated unit, the negatives
     * require exactly the pinned E6005.
     */
    private static SemanticLowerer.LoweringResult lowerSubject(
            CheckedProjectBuildResult checked, String modulePath) {
        CheckedModuleInput subject = moduleOf(checked.input(), modulePath);
        if (subject == null) {
            fail("the checked project has no module " + modulePath);
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation(),
            checked.input(), checked.index());
        check(manifests != null && !manifests.hasErrors(),
            "the manifest computation is clean"
                + (manifests == null ? " (null)" : ": " + manifests.diagnostics()));
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

    /**
     * Lowers the named subject module through the call-machine entry
     * (ISSUE-0659's retargeted drive): the resolved import facts and the
     * callee-route facts are installed, so the read and the typed-binding
     * invocation both lower and validate. A carrier session installs no
     * import facts and keeps failing closed through the unresolved-alias
     * guard.
     */
    private static SemanticLowerer.FullProgramE7Result lowerSubjectCallMachine(
            CheckedProjectBuildResult checked, String modulePath) {
        CheckedModuleInput subject = moduleOf(checked.input(), modulePath);
        if (subject == null) {
            fail("the checked project has no module " + modulePath);
            return null;
        }
        RequirementManifestResult manifests = LoweringSupport.computeManifests(invocation(),
            checked.input(), checked.index());
        check(manifests != null && !manifests.hasErrors(),
            "the manifest computation is clean"
                + (manifests == null ? " (null)" : ": " + manifests.diagnostics()));
        if (manifests == null || manifests.hasErrors()) {
            return null;
        }
        SemanticRequirementManifest manifest = manifestOf(manifests, subject.moduleId());
        if (manifest == null) {
            fail("no manifest for module " + modulePath);
            return null;
        }
        List<ModuleId> moduleIds = new ArrayList<>();
        Map<ModuleId, ModuleRoute> routes = new LinkedHashMap<>();
        for (CheckedModuleInput module : checked.input().modules()) {
            moduleIds.add(module.moduleId());
            routes.put(module.moduleId(), ModuleRoute.SHARED);
        }
        return SemanticLowerer.lowerModuleFullProgramE7(subject,
            SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
            checked.index().interfaceIndexDigest(),
            CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
            SemanticIdAllocator.over(moduleIds), routes, Map.of(), Set.of());
    }

    // =========================================================================
    // Op inspection helpers
    // =========================================================================

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
    private static SemanticOp stdlibOpBy(LoweredModuleUnit unit, StdlibFunctionId function) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.STDLIB_CALL
                    && ((KindPayload.StdlibCallPayload) op.payload()).function() == function) {
                return op;
            }
        }
        return null;
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

    /** The op producing the given value, or null. */
    private static SemanticOp producerOf(LoweredModuleUnit unit, ValueId value) {
        for (SemanticOp op : unit.ops()) {
            if (value.equals(op.result())) {
                return op;
            }
        }
        return null;
    }

    /** The position of an op in the unit op list, or -1. */
    private static int indexOf(LoweredModuleUnit unit, SemanticOp wanted) {
        for (int i = 0; i < unit.ops().size(); i++) {
            if (unit.ops().get(i).equals(wanted)) {
                return i;
            }
        }
        return -1;
    }

    /** The descriptor-kind rule of the closed boundary table. */
    private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
        return descriptor instanceof RuntimeDescriptor.Func
            ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
    }

    // =========================================================================
    // 1. The single-source policy table
    // =========================================================================

    /** The pinned 21-id algorithm→policy mapping of the task (an expectation mirror). */
    private static FailurePolicyId expectedPolicy(StdlibFunctionId function) {
        return switch (function) {
            case CONSOLE_LOG, CONSOLE_ERROR -> FailurePolicyId.INFRASTRUCTURE_ONLY;
            case STRING_LENGTH, MATH_ABS_INT, TIME_NOW_MILLIS -> FailurePolicyId.INT32_RESULT;
            case JSON_PARSE -> FailurePolicyId.JSON_PARSE_SYNTAX;
            case JSON_STRINGIFY -> FailurePolicyId.JSON_TO_ERROR;
            case MATH_SQRT -> FailurePolicyId.SQRT_NEGATIVE;
            default -> FailurePolicyId.NO_DEAL_FAILURE;
        };
    }

    static void testPolicyTableSingleSource() {
        System.out.println("-- Single source: SemanticIrValidator.stdlibPolicy --");

        check(StdlibFunctionId.values().length == 21,
            "the closed StdlibFunctionId enum is exactly 21 values (TIME_NOW_MILLIS is the "
                + "21st member)");
        for (StdlibFunctionId function : StdlibFunctionId.values()) {
            check(SemanticIrValidator.stdlibPolicy(function) == expectedPolicy(function),
                "stdlibPolicy(" + function + ") = "
                    + SemanticIrValidator.stdlibPolicy(function) + ", expected "
                    + expectedPolicy(function));
            check(!StdlibFunctionId.isReservedName(function.name()),
                function + " is never a reserved selector name");
        }
        check(StdlibFunctionId.RESERVED_NAMES.isEmpty(),
            "RESERVED_NAMES is empty (the superseded D8 reservation is retired) while the "
                + "reserved-name guard stays");
        check(SemanticIrValidator.stdlibPolicy(StdlibFunctionId.TIME_NOW_MILLIS)
                == FailurePolicyId.INT32_RESULT,
            "stdlibPolicy(TIME_NOW_MILLIS) = INT32_RESULT — the declared int boundary is "
                + "the single terminal");
        check(StdlibFunctionCatalog.lookup("std.time", "nowMillis")
                .map(entry -> entry.function() == StdlibFunctionId.TIME_NOW_MILLIS
                    && entry.parameterDescriptors().isEmpty())
                .orElse(false),
            "std/time.nowMillis is the closed zero-parameter catalog row (K7)");
        // The policy table is stable across calls (pure static surface).
        for (StdlibFunctionId function : StdlibFunctionId.values()) {
            check(SemanticIrValidator.stdlibPolicy(function)
                    == SemanticIrValidator.stdlibPolicy(function),
                "stdlibPolicy is pure and deterministic for " + function);
        }
    }

    // =========================================================================
    // 2. The all-id lowering battery
    // =========================================================================

    static void testLoweringBatteryAllIds() throws Exception {
        System.out.println("-- Lowering battery: all 21 ids, one validated STDLIB_CALL each --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-battery");
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
                    import * as tbl from "std/table"
                    import * as json from "std/json"
                    import * as math from "std/math"
                    import * as time from "std/time"

                    function run(): null {
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
                "the all-id battery lowers through the validator/chain protocol/"
                    + "control-flow validator: " + (lowering == null ? "null"
                        : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            LoweredModuleUnit unit = lowering.unit();

            List<SemanticOp> stdlibOps = stdlibOps(unit);
            check(stdlibOps.size() == 21,
                "exactly one STDLIB_CALL per cataloged call: 21 ops; got "
                    + stdlibOps.size());
            EnumSet<StdlibFunctionId> produced = EnumSet.noneOf(StdlibFunctionId.class);
            for (SemanticOp op : stdlibOps) {
                produced.add(((KindPayload.StdlibCallPayload) op.payload()).function());
            }
            check(produced.equals(EnumSet.allOf(StdlibFunctionId.class)),
                "the produced STDLIB_CALL function set equals the catalog's closed 21-id "
                    + "set (fails if the catalog misses or adds an entry); got " + produced);

            Map<StdlibFunctionId, Integer> counts = new LinkedHashMap<>();
            for (SemanticOp op : stdlibOps) {
                StdlibFunctionId function =
                    ((KindPayload.StdlibCallPayload) op.payload()).function();
                counts.merge(function, 1, Integer::sum);
                StdlibFunctionCatalog.Entry row = catalogEntryOf(function);
                Optional<StdlibFunctionCatalog.Entry> entry =
                    StdlibFunctionCatalog.lookup(row.modulePath(), row.exportName());
                check(entry.isPresent() && entry.get().equals(row),
                    "the produced " + function + " resolves to its closed catalog row");

                KindPayload.StdlibCallPayload payload =
                    (KindPayload.StdlibCallPayload) op.payload();

                // Payload: {function, args, effectCapability} — args in
                // the same left-to-right order as the operands.
                check(payload.effectCapability() == SemanticCapability.STDLIB_SEMANTICS,
                    function + " carries effectCapability STDLIB_SEMANTICS");
                check(payload.args().equals(op.operands()),
                    function + " payload args equal the op operands in order: "
                        + payload.args() + " vs " + op.operands());
                check(payload.args().size() == row.parameterDescriptors().size(),
                    function + " carries one argument per declared parameter ("
                        + row.parameterDescriptors().size() + "); got "
                        + payload.args().size());

                // Operand descriptors: the declared parameter descriptors in order.
                check(op.operandTypes().equals(row.parameterDescriptors()),
                    function + " operandTypes equal the declared parameter descriptors in "
                        + "order: " + op.operandTypes() + " vs "
                        + row.parameterDescriptors());

                // Result: one fresh value with the declared return descriptor.
                check(op.result() instanceof ValueId,
                    function + " publishes a ValueId result");
                check(op.resultType().equals(row.returnDescriptor()),
                    function + " resultType is the declared return descriptor "
                        + row.returnDescriptor().canonicalSpecText() + "; got "
                        + (op.resultType() == null ? "null"
                            : ((RuntimeDescriptor) op.resultType()).canonicalSpecText()));

                // The stamped policy: the single validator table, never a copy.
                check(op.failurePolicy() == SemanticIrValidator.stdlibPolicy(function),
                    function + " stamps failurePolicy "
                        + SemanticIrValidator.stdlibPolicy(function) + " from the single "
                        + "validator table; got " + op.failurePolicy());

                // Boundary children: one STDLIB_PARAMETER per declared
                // parameter in one-based order, then the single
                // STDLIB_RETURN — declared descriptors, descriptor-kind
                // rule; no other boundary ops.
                List<SemanticOp> children = childrenOf(unit, op.opId());
                check(children.size() == row.parameterDescriptors().size() + 1,
                    function + " has exactly " + (row.parameterDescriptors().size() + 1)
                        + " boundary children (" + row.parameterDescriptors().size()
                        + " parameters + 1 return); got " + children.size());
                int boundaryChildren = 0;
                for (int i = 0; i < children.size(); i++) {
                    SemanticOp child = children.get(i);
                    check(child.kind() == SemanticOpKind.BOUNDARY,
                        function + " child " + i + " is a BOUNDARY op");
                    if (child.kind() != SemanticOpKind.BOUNDARY) {
                        continue;
                    }
                    boundaryChildren++;
                    KindPayload.BoundaryPayload boundary =
                        (KindPayload.BoundaryPayload) child.payload();
                    if (i < row.parameterDescriptors().size()) {
                        check(boundary.kind() == BoundaryKind.STDLIB_PARAMETER,
                            function + " child " + i + " is STDLIB_PARAMETER in one-based "
                                + "order; got " + boundary.kind());
                        check(boundary.descriptor().equals(
                                row.parameterDescriptors().get(i)),
                            function + " parameter boundary " + i + " carries the declared "
                                + "descriptor " + row.parameterDescriptors().get(i)
                                + "; got " + boundary.descriptor());
                        check(boundary.input().equals(op.operands().get(i)),
                            function + " parameter boundary " + i + " input is the "
                                + "argument ValueId in order");
                    } else {
                        check(boundary.kind() == BoundaryKind.STDLIB_RETURN,
                            function + " child " + i + " is the single STDLIB_RETURN "
                                + "boundary; got " + boundary.kind());
                        check(boundary.descriptor().equals(row.returnDescriptor()),
                            function + " return boundary carries the declared return "
                                + "descriptor " + row.returnDescriptor()
                                + "; got " + boundary.descriptor());
                        check(boundary.input().equals(op.result()),
                            function + " return boundary input is the call result");
                    }
                    check(child.failurePolicy()
                            == descriptorKindPolicy(boundary.descriptor()),
                        function + " boundary child " + i + " carries the descriptor-kind "
                            + "rule policy " + descriptorKindPolicy(boundary.descriptor())
                            + "; got " + child.failurePolicy());
                }
                check(boundaryChildren == children.size(),
                    function + " has no non-boundary children");

                // The member access's checked export read precedes the
                // STDLIB_CALL and its function identity is registered
                // (R-FUNCTION-BINDING holds by construction).
                int exportReads = 0;
                int opIndex = indexOf(unit, op);
                boolean registered = false;
                for (SemanticOp candidate : unit.ops()) {
                    if (candidate.kind() == SemanticOpKind.EXPORT_READ) {
                        KindPayload.ExportReadPayload read =
                            (KindPayload.ExportReadPayload) candidate.payload();
                        if (read.module().path().equals(row.modulePath())
                                && read.name().equals(row.exportName())) {
                            exportReads++;
                            check(indexOf(unit, candidate) < opIndex,
                                function + "'s export read precedes the STDLIB_CALL");
                            FunctionExecutionBinding binding =
                                unit.functionBindings().get(
                                    new FunctionAllocationIdentity(read.value().id()));
                            check(binding instanceof FunctionExecutionBinding.HostFunction
                                    && ((FunctionExecutionBinding.HostFunction) binding)
                                        .exportName().equals(row.exportName()),
                                function + "'s export read registers its HostFunction "
                                    + "binding");
                            registered = true;
                        }
                    }
                }
                check(exportReads == 1 && registered,
                    function + " emits exactly one EXPORT_READ of the cataloged export "
                        + "with a registered function binding; got " + exportReads);
            }
            for (Map.Entry<StdlibFunctionId, Integer> entry : counts.entrySet()) {
                check(entry.getValue() == 1,
                    "exactly one STDLIB_CALL per id (" + entry.getKey() + "); got "
                        + entry.getValue());
            }

            // The unit passes the closed validator on both surfaces.
            Optional<CompilerDiagnostic> typed =
                SemanticIrValidator.validate(unit, factsOf(checked));
            check(typed.isEmpty(),
                "the battery unit passes the closed validator on the typed surface"
                    + (typed.isPresent() ? ": " + typed.get().message() : ""));
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** The closed catalog row of one id (the single row carrying it). */
    private static StdlibFunctionCatalog.Entry catalogEntryOf(StdlibFunctionId function) {
        for (StdlibFunctionCatalog.Entry entry : StdlibFunctionCatalog.entries()) {
            if (entry.function() == function) {
                return entry;
            }
        }
        throw new IllegalStateException("no catalog row for " + function);
    }

    // =========================================================================
    // 3. Argument operand completion order
    // =========================================================================

    static void testArgumentOperandCompletionOrder() throws Exception {
        System.out.println("-- Argument operand completion: left-to-right before START --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-order");
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

                    function markS(v: string): string { console.log("s"); return v; }
                    function markB(v: int): int { console.log("b"); return v; }
                    function markC(v: int): int { console.log("c"); return v; }

                    function run(): null {
                      let s: string = str.substring(markS("ab"), markB(0), markC(1))
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
                "the side-effecting argument battery lowers through the validator/"
                    + "chain protocol/control-flow validator: " + (lowering == null
                        ? "null" : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            LoweredModuleUnit unit = lowering.unit();

            SemanticOp call = stdlibOpBy(unit, StdlibFunctionId.STRING_SUBSTRING);
            check(call != null, "the module produces the STRING_SUBSTRING STDLIB_CALL");
            if (call == null) {
                return;
            }
            check(call.operands().size() == 3,
                "the substring call completes 3 argument operands; got "
                    + call.operands().size());
            String[] marks = {"s", "b", "c"};
            int previous = -1;
            int callIndex = indexOf(unit, call);
            for (int i = 0; i < call.operands().size(); i++) {
                SemanticOp producer = producerOf(unit, call.operands().get(i));
                check(producer != null && producer.kind() == SemanticOpKind.CALL,
                    "argument " + i + " is produced by a CALL op (the mark call)");
                if (producer == null || producer.kind() != SemanticOpKind.CALL) {
                    continue;
                }
                KindPayload.CallPayload callPayload =
                    (KindPayload.CallPayload) producer.payload();
                check(bodyContainsConst(unit, lowering.table(), callPayload, marks[i]),
                    "argument " + i + " produces the call of the marker whose body logs '"
                        + marks[i] + "'");
                int producerIndex = indexOf(unit, producer);
                check(producerIndex > previous,
                    "argument operands complete left-to-right: argument " + i
                        + " producer position " + producerIndex + " after "
                        + previous);
                check(producerIndex < callIndex,
                    "argument " + i + " completes before the STDLIB_CALL START (position "
                        + producerIndex + " < " + callIndex + ")");
                previous = producerIndex;
            }
            // The three console marks inside the mark bodies are
            // STDLIB_CALL(CONSOLE_LOG)s whose arguments are the pinned
            // literals — the side effects themselves.
            int consoleLogs = 0;
            for (SemanticOp op : stdlibOps(unit)) {
                if (((KindPayload.StdlibCallPayload) op.payload()).function()
                        == StdlibFunctionId.CONSOLE_LOG) {
                    consoleLogs++;
                }
            }
            check(consoleLogs == 3,
                "the three mark calls each lower one CONSOLE_LOG STDLIB_CALL; got "
                    + consoleLogs);
        } finally {
            deleteRecursively(tmp);
        }
    }

    /**
     * The body block of a DIRECT call's callee contains a CONST with the
     * given string literal — the structural fingerprint linking the call
     * op to the mark function logging that literal (the block-membership
     * table is the produced {@link StructuredBodyTable}).
     */
    private static boolean bodyContainsConst(LoweredModuleUnit unit,
            deal.semantic.ir.StructuredBodyTable table, KindPayload.CallPayload callPayload,
            String literal) {
        if (!(callPayload.callee() instanceof KindPayload.CallCallee.Static staticCallee)
                || !(staticCallee.binding()
                    instanceof FunctionExecutionBinding.LoweredBody body)) {
            return false;
        }
        List<OpId> blockOps = table.blockOps().get(body.blockId());
        if (blockOps == null) {
            return false;
        }
        for (OpId opId : blockOps) {
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(opId) && op.kind() == SemanticOpKind.CONST
                        && op.payload() instanceof KindPayload.ConstPayload constant
                        && constant.value() instanceof deal.semantic.ir.ScalarValue.String string
                        && literal.equals(string.value())) {
                    return true;
                }
            }
        }
        return false;
    }

    // =========================================================================
    // 4. Negatives: no STDLIB_CALL for non-cataloged callees
    // =========================================================================

    static void testNegativeUserModuleMemberCall() throws Exception {
        System.out.println("-- Negative: user-module member call produces no STDLIB_CALL --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-user");
        try {
            CheckedProjectBuildResult checked = compileProject(tmp, Map.of(
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
            if (checked == null) {
                return;
            }
            CheckedModuleInput main = moduleOf(checked.input(), "lib");
            check(main != null, "the checked project contains module lib");
            if (main == null) {
                return;
            }
            // The call site is recognized as no stdlib call (the import's
            // resolved module is IMPLEMENTATION, never STDLIB).
            CallExpr call = firstCallIn(main, "run");
            check(call != null && call.callee() instanceof MemberAccessExpr,
                "main calls the member s.length");
            if (call == null) {
                return;
            }
            SymbolTable scope = scopeAt(main, call);
            check(StdlibCallRecognition.recognize(call.callee(), scope, main.imports())
                    .isEmpty(),
                "s.length on a user-module import is never recognized as a stdlib call");
            // The lowering fails with the generic direct-call shape E6005
            // and produces no unit, hence zero STDLIB_CALL ops.
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && lowering.hasErrors() && lowering.unit() == null,
                "the user-module member call fails lowering with no unit (E6005)");
            if (lowering != null && lowering.hasErrors()) {
                check(lowering.diagnostics().stream().anyMatch(diagnostic ->
                        diagnostic.message().contains("call callee shape MemberAccessExpr")),
                    "the failure is the generic non-direct call shape, never a stdlib "
                        + "production: " + lowering.diagnostics());
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    static void testNegativeStdlibExportValueRead() throws Exception {
        System.out.println("-- The stdlib value read realizes through the call machine "
            + "(D3) --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-valueread");
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
            // The value read claims no capability: the manifest gains no
            // stdlib row from the read.
            RequirementManifestResult manifests = LoweringSupport.computeManifests(
                invocation(), checked.input(), checked.index());
            SemanticRequirementManifest manifest = manifestOf(manifests,
                moduleOf(checked.input(), "lib").moduleId());
            check(manifest != null
                    && !manifest.capabilities().contains(SemanticCapability.STDLIB_SEMANTICS),
                "the value-read module's manifest claims no STDLIB_SEMANTICS from the read"
                    + (manifest == null ? " (no manifest)" : ": " + manifest.capabilities()));
            // The realized lowering: the read and the typed-binding
            // invocation both lower and validate through the call-machine
            // entry (the resolved import facts and the callee-route facts
            // are installed by that drive). No "no unit" state is
            // asserted for the fixture.
            SemanticLowerer.FullProgramE7Result result =
                lowerSubjectCallMachine(checked, "lib");
            check(result != null && result.lowering() != null
                    && !result.lowering().hasErrors()
                    && result.lowering().unit() != null,
                "the fixture lowers to a validated unit through the call machine"
                    + (result == null || result.lowering() == null ? " (null)"
                        : ": " + result.lowering().diagnostics()));
            if (result == null || result.lowering() == null
                    || result.lowering().hasErrors() || result.lowering().unit() == null) {
                return;
            }
            LoweredModuleUnit unit = result.lowering().unit();
            List<SemanticOp> reads = new ArrayList<>();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.EXPORT_READ) {
                    reads.add(op);
                }
            }
            check(reads.size() == 1,
                "exactly one EXPORT_READ is produced for the read occurrence; got "
                    + reads.size());
            if (reads.size() != 1) {
                return;
            }
            KindPayload.ExportReadPayload payload =
                (KindPayload.ExportReadPayload) reads.get(0).payload();
            StdlibFunctionCatalog.Entry row = StdlibFunctionCatalog
                .lookup("std.console", "log").orElseThrow();
            RuntimeDescriptor.Func rowDescriptor = new RuntimeDescriptor.Func(
                row.parameterDescriptors(), row.returnDescriptor());
            check(payload.module().path().equals("std.console")
                    && payload.name().equals("log")
                    && payload.descriptor().equals(rowDescriptor),
                "the read names std.console/log with the catalog row's declared descriptor "
                    + rowDescriptor.canonicalSpecText() + "; got " + payload.module()
                    + "/" + payload.name() + " "
                    + payload.descriptor().canonicalSpecText());
            FunctionExecutionBinding binding = unit.functionBindings().get(
                new FunctionAllocationIdentity(payload.value().id()));
            check(binding instanceof FunctionExecutionBinding.HostFunction host
                    && host.hostModuleId().path().equals("std.console")
                    && host.exportName().equals("log")
                    && host.descriptor().equals(rowDescriptor),
                "exactly one HostFunction(std.console, log, row descriptor) registration "
                    + "keyed by the read's result identity; got " + binding);
            // The typed-binding invocation of the read value lowers through
            // the landed call machine: CALL(INDIRECT) with the Static host
            // binding and the host cell family, admitted by the validator
            // (this drive validated the unit above).
            boolean indirect = unit.ops().stream().anyMatch(op ->
                op.kind() == SemanticOpKind.CALL
                    && ((KindPayload.CallPayload) op.payload()).callee()
                        instanceof KindPayload.CallCallee.Static
                    && ((KindPayload.CallPayload) op.payload()).mode()
                        == deal.semantic.ir.CallMode.INDIRECT);
            check(indirect,
                "the read value's invocation lowers CALL(INDIRECT) with the Static "
                    + "binding");
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** The first call expression in the named function's body, or null. */
    private static CallExpr firstCallIn(CheckedModuleInput module, String functionName) {
        for (StatementNode stmt : module.ast().statements()) {
            StatementNode declared = stmt instanceof ExportDeclaration export
                ? export.declaration() : stmt;
            if (declared instanceof FunctionDeclaration function
                    && function.name().equals(functionName)) {
                for (StatementNode bodyStmt : function.body().statements()) {
                    if (bodyStmt instanceof VariableDeclaration decl
                            && decl.initializer() instanceof CallExpr call) {
                        return call;
                    }
                    if (bodyStmt instanceof deal.ast.ExpressionStatement expressionStatement
                            && expressionStatement.expr() instanceof CallExpr call) {
                        return call;
                    }
                }
            }
        }
        return null;
    }

    /** The checker scope at a call site: the innermost scope-keyed statement's table. */
    private static SymbolTable scopeAt(CheckedModuleInput module, CallExpr call) {
        Map<StatementNode, SymbolTable> scopeMap = module.checks().scopeMap();
        for (StatementNode stmt : module.ast().statements()) {
            StatementNode declared = stmt instanceof ExportDeclaration export
                ? export.declaration() : stmt;
            if (!(declared instanceof FunctionDeclaration function)
                    || !function.name().equals("run")) {
                continue;
            }
            for (StatementNode bodyStmt : function.body().statements()) {
                if (bodyStmt instanceof VariableDeclaration decl
                        && decl.initializer() == call) {
                    SymbolTable scope = scopeMap.get(decl);
                    if (scope != null) {
                        return scope;
                    }
                    scope = scopeMap.get(function.body());
                    if (scope != null) {
                        return scope;
                    }
                    return module.checks().symbolTable();
                }
                if (bodyStmt instanceof deal.ast.ExpressionStatement expressionStatement
                        && expressionStatement.expr() == call) {
                    SymbolTable scope = scopeMap.get(expressionStatement);
                    if (scope != null) {
                        return scope;
                    }
                    scope = scopeMap.get(function.body());
                    if (scope != null) {
                        return scope;
                    }
                    return module.checks().symbolTable();
                }
            }
        }
        return module.checks().symbolTable();
    }

    // =========================================================================
    // 5. Validator conformance: a wrong stamped policy fails
    // =========================================================================

    static void testWrongPolicyValidatorFailure() throws Exception {
        System.out.println("-- Validator: a hand-modified wrong stamped policy fails --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-wrongpolicy");
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
                "the wrong-policy battery lowers through the validator/chain protocol/"
                    + "control-flow validator: " + (lowering == null ? "null"
                        : lowering.diagnostics()));
            if (lowering == null || lowering.hasErrors() || lowering.unit() == null) {
                return;
            }
            LoweredModuleUnit unit = lowering.unit();
            SemanticOp call = stdlibOpBy(unit, StdlibFunctionId.STRING_LENGTH);
            check(call != null
                    && call.failurePolicy() == FailurePolicyId.INT32_RESULT,
                "the produced STRING_LENGTH stamps INT32_RESULT from the single table");
            if (call == null) {
                return;
            }
            SemanticIrValidator.ComparisonFacts facts = factsOf(checked);

            // Positive control: the unmodified unit passes both surfaces.
            Optional<CompilerDiagnostic> untouched =
                SemanticIrValidator.validate(unit, facts);
            check(untouched.isEmpty(),
                "the untouched unit passes the closed validator"
                    + (untouched.isPresent() ? ": " + untouched.get().message() : ""));

            // Hand-modified raw unit: the STDLIB_CALL's stamped policy is
            // replaced by NO_DEAL_FAILURE (wrong for STRING_LENGTH) in the
            // op position and in its contract snapshot, with the digest
            // recomputed — the only defect is the policy itself.
            RawUnit raw = RawUnit.fromTyped(unit);
            List<RawOp> modified = new ArrayList<>();
            for (RawOp op : raw.ops()) {
                if (SemanticOpKind.STDLIB_CALL.name().equals(op.kind())
                        && "STRING_LENGTH".equals(
                            ContractSnapshotCanonicalizer.optionalString(op.payload(),
                                "function"))) {
                    modified.add(withStampedPolicy(op, "NO_DEAL_FAILURE"));
                } else {
                    modified.add(op);
                }
            }
            RawUnit modifiedUnit = new RawUnit(raw.modulePath(), raw.semanticProfile(),
                raw.interfaceHash(), raw.loweringContextHash(), raw.requiredCapabilities(),
                raw.coverage(), raw.bindings(), modified);
            String modifiedText = ContractSnapshotCanonicalizer.serializeText(
                ContractSnapshotCanonicalizer.toJson(modifiedUnit));
            Optional<CompilerDiagnostic> wrongPolicy =
                SemanticIrValidator.validateText(modifiedText, facts);
            check(wrongPolicy.isPresent(),
                "the wrong stamped policy fails validation through the text surface");
            if (wrongPolicy.isPresent()) {
                check(wrongPolicy.get().message().contains("R-POLICY-KIND")
                        && wrongPolicy.get().message().contains("STRING_LENGTH"),
                    "the failure is R-POLICY-KIND on STRING_LENGTH (the closed "
                        + "algorithm→policy check): " + wrongPolicy.get().message());
            }

            // The same modification on the op position alone (snapshot and
            // digest untouched) is still caught by the same rule.
            RawUnit opOnlyRaw = RawUnit.fromTyped(unit);
            List<RawOp> opOnlyModified = new ArrayList<>();
            for (RawOp op : opOnlyRaw.ops()) {
                if (SemanticOpKind.STDLIB_CALL.name().equals(op.kind())
                        && "STRING_LENGTH".equals(
                            ContractSnapshotCanonicalizer.optionalString(op.payload(),
                                "function"))) {
                    opOnlyModified.add(new RawOp(op.opId(), op.kind(), "NO_DEAL_FAILURE",
                        op.parentOpId(), op.resultValue(), op.resultToken(),
                        op.resultType(), op.operands(), op.operandTypes(), op.payload(),
                        op.selector(), op.canonicalDigest(), op.snapshot()));
                } else {
                    opOnlyModified.add(op);
                }
            }
            RawUnit opOnlyUnit = new RawUnit(opOnlyRaw.modulePath(),
                opOnlyRaw.semanticProfile(), opOnlyRaw.interfaceHash(),
                opOnlyRaw.loweringContextHash(), opOnlyRaw.requiredCapabilities(),
                opOnlyRaw.coverage(), opOnlyRaw.bindings(), opOnlyModified);
            Optional<CompilerDiagnostic> opOnlyFailure = SemanticIrValidator.validateText(
                ContractSnapshotCanonicalizer.serializeText(
                    ContractSnapshotCanonicalizer.toJson(opOnlyUnit)),
                facts);
            check(opOnlyFailure.isPresent()
                    && opOnlyFailure.get().message().contains("R-POLICY-KIND"),
                "an op-position-only wrong policy fails R-POLICY-KIND too: "
                    + opOnlyFailure.map(CompilerDiagnostic::message).orElse("none"));
        } finally {
            deleteRecursively(tmp);
        }
    }

    /** One raw op with its stamped policy (op + snapshot) replaced and the digest recomputed. */
    private static RawOp withStampedPolicy(RawOp op, String policyName) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : op.snapshot().entries()) {
            if (entry.key().equals("failurePolicy")) {
                entries.add(CanonicalJson.e("failurePolicy", CanonicalJson.str(policyName)));
            } else {
                entries.add(entry);
            }
        }
        CanonicalJson.Obj snapshot = CanonicalJson.obj(entries);
        String digest = ContractSnapshotCanonicalizer.recomputeSnapshotDigest(snapshot);
        return new RawOp(op.opId(), op.kind(), policyName, op.parentOpId(), op.resultValue(),
            op.resultToken(), op.resultType(), op.operands(), op.operandTypes(), op.payload(),
            op.selector(), digest, snapshot);
    }

    // =========================================================================
    // 6. Dump determinism and the stdlib payload fields
    // =========================================================================

    static void testDumpDeterminismAndPayloadFields() throws Exception {
        System.out.println("-- Dump determinism: byte-identical text with the stdlib payload --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-dump");
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
                    import * as json from "std/json"
                    import * as math from "std/math"

                    function run(): null {
                      console.log("hi")
                      let t: table = json.parse("{\\"k\\": 1}")
                      let s: string = json.stringify(t)
                      let f: number = math.floor(1.5)
                      let i: int = math.absInt(-3)
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
            // Re-lowering the same module twice produces byte-identical
            // deal.semantic-ir/1 text (fresh sessions, fresh allocators).
            CheckedModuleInput main = moduleOf(checked.input(), "lib");
            RequirementManifestResult manifests = LoweringSupport.computeManifests(
                invocation(), checked.input(), checked.index());
            SemanticRequirementManifest manifest = manifestOf(manifests, main.moduleId());
            List<ModuleId> moduleIds = new ArrayList<>();
            for (CheckedModuleInput module : checked.input().modules()) {
                moduleIds.add(module.moduleId());
            }
            SemanticLowerer.LoweringResult first = SemanticLowerer.lowerModuleFullProgram(
                main, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
                checked.index().interfaceIndexDigest(),
                CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
                SemanticIdAllocator.over(moduleIds));
            SemanticLowerer.LoweringResult second = SemanticLowerer.lowerModuleFullProgram(
                main, SemanticProfile.DEAL_V1_2_INT32, manifest.constructCoverage(),
                checked.index().interfaceIndexDigest(),
                CapabilityRegistry.releaseRegistry().capabilityRegistryHash(),
                SemanticIdAllocator.over(moduleIds));
            check(first != null && !first.hasErrors() && second != null
                    && !second.hasErrors(),
                "both re-lowerings succeed (fresh allocators)");
            if (first == null || first.hasErrors() || second == null
                    || second.hasErrors()) {
                return;
            }
            byte[] dump1 = SemanticIrDumper.dumpModule(first.unit());
            byte[] dump2 = SemanticIrDumper.dumpModule(second.unit());
            check(java.util.Arrays.equals(dump1, dump2),
                "re-lowering the same module produces byte-identical "
                    + "deal.semantic-ir/1 text");
            byte[] again = SemanticIrDumper.dumpModule(first.unit());
            check(java.util.Arrays.equals(dump1, again),
                "repeated dumps of the same unit are byte-identical");
            String text = SemanticIrDumper.dumpModuleText(first.unit());
            check(text.contains("\"kind\":\"STDLIB_CALL\""),
                "the dump serializes the STDLIB_CALL op kind");
            check(text.contains("\"effectCapability\":\"STDLIB_SEMANTICS\""),
                "the dump serializes the payload effectCapability");
            check(text.contains("\"args\""),
                "the dump serializes the payload args field");
            for (StdlibFunctionId function : List.of(StdlibFunctionId.CONSOLE_LOG,
                    StdlibFunctionId.JSON_PARSE, StdlibFunctionId.JSON_STRINGIFY,
                    StdlibFunctionId.MATH_FLOOR, StdlibFunctionId.MATH_ABS_INT)) {
                check(text.contains("\"function\":\"" + function.name() + "\""),
                    "the dump carries the payload function " + function);
            }
            check(text.contains("\"kind\":\"STDLIB_PARAMETER\"")
                    && text.contains("\"kind\":\"STDLIB_RETURN\""),
                "the dump carries the STDLIB_PARAMETER/STDLIB_RETURN boundary kinds");
            check(text.contains("\"STDLIB_SEMANTICS\""),
                "the required/effect capability spelling is serialized");
            Optional<CompilerDiagnostic> textValidation = SemanticIrValidator.validateText(
                text, factsOf(checked));
            check(textValidation.isEmpty(),
                "the dumped text re-validates through the validator's text surface"
                    + (textValidation.isPresent() ? ": " + textValidation.get().message()
                        : ""));
            // The typed unit itself passes the closed validator.
            Optional<CompilerDiagnostic> typed = SemanticIrValidator.validate(first.unit(),
                factsOf(checked));
            check(typed.isEmpty(),
                "the dumped unit passes the closed validator on the typed surface"
                    + (typed.isPresent() ? ": " + typed.get().message() : ""));
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================
    // 7. The K7 time slice: std/time.nowMillis reaches the stdlib branch
    // =========================================================================

    static void testTimeRowRouteAndRecognition() throws Exception {
        System.out.println("-- Time row: std/time.nowMillis reaches the stdlib branch (K7) --");

        Path tmp = Files.createTempDirectory("deal-stdlib-call-time");
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
            CheckedModuleInput main = moduleOf(checked.input(), "lib");
            check(main != null, "the checked project contains module lib");
            if (main == null) {
                return;
            }
            CallExpr call = firstCallIn(main, "run");
            check(call != null && call.callee() instanceof MemberAccessExpr,
                "main calls the std/time member nowMillis");
            if (call != null) {
                check(StdlibCallRecognition.recognize(call.callee(), scopeAt(main, call),
                        main.imports())
                        .map(StdlibFunctionCatalog.Entry::function)
                        .orElse(null) == StdlibFunctionId.TIME_NOW_MILLIS,
                    "t.nowMillis is recognized through the closed std.time/nowMillis "
                        + "catalog row (K7)");
            }

            // The claim slice: the module claims STDLIB_SEMANTICS through the
            // landed cataloged-call arm and never the inert
            // STDLIB_TIME_CONFLICT marker; the recognized time construct
            // records its own coverage row.
            RequirementManifestResult manifests = LoweringSupport.computeManifests(
                invocation(), checked.input(), checked.index());
            SemanticRequirementManifest manifest = manifestOf(manifests, main.moduleId());
            check(manifest != null
                    && manifest.capabilities().contains(
                        SemanticCapability.STDLIB_SEMANTICS),
                "the std/time-importing module's manifest claims STDLIB_SEMANTICS "
                    + "(the cataloged-call arm)"
                    + (manifest == null ? " (no manifest)" : ": " + manifest.capabilities()));
            check(manifest != null
                    && !manifest.capabilities().contains(
                        SemanticCapability.STDLIB_TIME_CONFLICT),
                "no manifest claims STDLIB_TIME_CONFLICT (the superseded four-part "
                    + "trigger is retired)"
                    + (manifest == null ? " (no manifest)" : ": " + manifest.capabilities()));
            check(manifest != null && manifest.constructCoverage()
                    .containsKey(deal.semantic.ir.ConstructKind.STDLIB_TIME_NOW_MILLIS),
                "the manifest records the STDLIB_TIME_NOW_MILLIS coverage row");
            {
                RoutePlanResult planned = MigrationPlanner.planRoutes(invocation(),
                    CapabilityRegistry.releaseRegistry(), checked.input(), checked.index(),
                    manifests.manifests(), Target.LUAJIT, Set.of(main.moduleId()));
                check(planned != null && planned.diagnostics().isEmpty()
                        && planned.plan() != null,
                    "the route plan computes cleanly for the time module");
                if (planned != null && planned.plan() != null) {
                    check(planned.plan().entries().get(main.moduleId())
                            == ModuleRoute.SHARED
                            && planned.plan().shadowModules().contains(main.moduleId()),
                        "the time module is no longer forced LEGACY by a conflict claim: "
                            + "the COMMON_SHADOW request common-lowers it (recorded shadow) — "
                            + "the retired rule 2 never fires, and the planner's "
                            + "time-conflict reroute stays in the tree inert");
                }
            }

            // A direct forced lowering drive produces the K7 shape: one
            // STDLIB_CALL(TIME_NOW_MILLIS) with zero parameter boundaries,
            // one STDLIB_RETURN on the declared int, and the INT32_RESULT
            // terminal at the call origin.
            SemanticLowerer.LoweringResult lowering = lowerSubject(checked, "lib");
            check(lowering != null && !lowering.hasErrors() && lowering.unit() != null,
                "the forced lowering of the time module produces a validated unit: "
                    + (lowering == null ? "null" : lowering.diagnostics()));
            if (lowering != null && !lowering.hasErrors() && lowering.unit() != null) {
                SemanticOp timeOp = stdlibOpBy(lowering.unit(),
                    StdlibFunctionId.TIME_NOW_MILLIS);
                check(timeOp != null,
                    "the unit carries exactly one STDLIB_CALL(TIME_NOW_MILLIS)");
                if (timeOp != null) {
                    check(timeOp.failurePolicy() == FailurePolicyId.INT32_RESULT,
                        "the op stamps the INT32_RESULT terminal from the single "
                            + "stdlibPolicy table; got " + timeOp.failurePolicy());
                    check(timeOp.operands().isEmpty() && timeOp.operandTypes().isEmpty(),
                        "the zero-parameter row produces no parameter operands");
                    List<SemanticOp> children = childrenOf(lowering.unit(), timeOp.opId());
                    int returns = 0;
                    int params = 0;
                    for (SemanticOp child : children) {
                        if (child.kind() != SemanticOpKind.BOUNDARY) {
                            continue;
                        }
                        KindPayload.BoundaryPayload boundary =
                            (KindPayload.BoundaryPayload) child.payload();
                        if (boundary.kind() == BoundaryKind.STDLIB_RETURN) {
                            returns++;
                            check(boundary.descriptor().equals(
                                    DescriptorService.describe(Type.Int.INSTANCE)),
                                "the STDLIB_RETURN boundary carries the declared int "
                                    + "descriptor");
                        } else if (boundary.kind() == BoundaryKind.STDLIB_PARAMETER) {
                            params++;
                        }
                    }
                    check(returns == 1 && params == 0,
                        "exactly one STDLIB_RETURN and zero STDLIB_PARAMETER children; got "
                            + returns + "/" + params);
                    check(lowering.unit().constructCoverage()
                            .containsKey(deal.semantic.ir.ConstructKind
                                .STDLIB_TIME_NOW_MILLIS),
                        "the lowered unit records the STDLIB_TIME_NOW_MILLIS coverage "
                            + "row and R-COVERAGE applies to it");
                }
            }
        } finally {
            deleteRecursively(tmp);
        }
    }

    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Stdlib STDLIB_CALL Lowering Tests (ISSUE-0494) ===\n");

        testPolicyTableSingleSource();
        testLoweringBatteryAllIds();
        testArgumentOperandCompletionOrder();
        testNegativeUserModuleMemberCall();
        testNegativeStdlibExportValueRead();
        testWrongPolicyValidatorFailure();
        testDumpDeterminismAndPayloadFields();
        testTimeRowRouteAndRecognition();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
