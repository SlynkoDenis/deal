package deal.test;

import deal.checker.BuiltinErrorDeclaration;
import deal.codegen.Backend;
import deal.codegen.jvm.JvmSemanticEmitter;
import deal.codegen.lua.LuaSemanticEmitter;
import deal.diagnostics.CompilerDiagnostic;
import deal.identity.CanonicalModuleIdentity;
import deal.module.CompilationOrchestrator;
import deal.semantic.CheckedProjectBuildResult;
import deal.semantic.CheckedProjectInput;
import deal.semantic.CompilerInvocation;
import deal.semantic.CompilerProfileProvider;
import deal.semantic.HostDeclarationSurface;
import deal.semantic.ReleaseConfiguration;
import deal.semantic.RequirementManifestResult;
import deal.semantic.SemanticRequirementManifest;
import deal.semantic.SemanticLowerer;
import deal.semantic.SemanticRuntimeModel;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.OpId;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0679: the conversion intrinsic's value call — the closed static-callee
 * shape admission, the host cell family, the argument domain, and the ladder
 * with the invoking op's context and kind (design sources
 * {@code conversion-intrinsic-function-values} J3/J4 and the first-class
 * conversion intrinsic contract; {@code function-typed-value-materialization-
 * and-dispatch} M5's intrinsic HOST sub-class).
 *
 * <ol>
 *   <li><b>The nested static-callee shape admission.</b> The closed nested
 *       binding-shape enumeration admits {@code intrinsicFunction} for the
 *       static callee position, so the design's
 *       {@code CallCallee.Static(IntrinsicFunction)} payload validates instead
 *       of failing R-ENUM; the admitted shape keeps the shape position's
 *       closed discipline (the kind resolves in the closed {@code IntrinsicKind}
 *       set and both the kind and the descriptor positions are present), so a
 *       doctored nested payload violating any of those still fails the closed
 *       gate, and no other nested binding shape is newly admitted.</li>
 *   <li><b>The indirect arm's host cell family.</b> The indirect call of an
 *       {@code IntrinsicFunction} registration records one {@code DEAL_TO_HOST}
 *       + {@code HOST_PARAMETER} cell per declared parameter and the single
 *       {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} return cell, and the
 *       validator's indirect cell switch pins that family; the unit passes the
 *       closed gate and the closed bindings gate.</li>
 *   <li><b>The ladder with the invoking op's context and kind.</b> The oracle,
 *       the LuaJIT artifact under real {@code luajit}, and the JVM artifact
 *       under {@code javac --release 25 -proc:none} plus {@code java} project
 *       the pinned texts at the call origin with the invoking CALL op's kind in
 *       the FAILURE event; a valid input converts exactly.</li>
 *   <li><b>The argument domain.</b> The recorded parameter cells own it: the
 *       static indirect arm's {@code DEAL_TO_HOST} + {@code HOST_PARAMETER}
 *       cells check the intrinsic's declared parameter descriptor under their
 *       pinned E8010 row; the dynamic arm's class-independent
 *       {@code FUNCTION_PARAMETER} cells check the declared signature under the
 *       descriptor-kind rule. The direct {@code INTRINSIC_CALL} arm keeps its
 *       own kind label and its nullable overloads.</li>
 *   <li><b>The dynamic arm.</b> A function-typed parameter callee holding the
 *       intrinsic resolves the HOST class from the carrier's own tag on both
 *       targets and runs the same conversion with the call op's own context,
 *       then the recorded host cell.</li>
 * </ol>
 */
public class IntrinsicValueCallTest {

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

    private static void checkEq(Object expected, Object actual, String message) {
        check(java.util.Objects.equals(expected, actual), message + " (expected "
            + expected + ", got " + actual + ")");
    }

    private static void fail(String message) {
        failed++;
        System.err.println("FAIL: " + message);
    }

    private static final ModuleId APP = new ModuleId("app");

    // =========================================================================
    // Fixtures
    // =========================================================================

    /** The typed-binding drive (the corpus's intrinsic-as-function-value). */
    private static final String VALUE_SOURCE = """
        export function main(): null {
          let f: (x: number) => int = int;
          let result: int = f(3.0);
          if (result !== 3) {
            throw { code: "TEST_FAIL", message: "intrinsic value call" };
          }
          return null;
        }
        """;

    /** The callback drive (the corpus's intrinsic-as-callback). */
    private static final String CALLBACK_SOURCE = """
        function apply(f: (x: int) => number, x: int): number {
          return f(x);
        }

        export function main(): null {
          let result: number = apply(number, 7);
          if (result !== 7.0) {
            throw { code: "TEST_FAIL", message: "intrinsic callback" };
          }
          return null;
        }
        """;

    /** A NaN argument at a value call (INT_CONVERT's first reachable row). */
    private static final String NAN_SOURCE = """
        export function main(): null {
          let f: (x: number) => int = int;
          let z: number = 0.0;
          let n: number = z / z;
          let r: int = f(n);
          return null;
        }
        """;

    /** An infinity argument at a value call. */
    private static final String INFINITY_SOURCE = """
        export function main(): null {
          let f: (x: number) => int = int;
          let one: number = 1.0;
          let zero: number = 0.0;
          let r: int = f(one / zero);
          return null;
        }
        """;

    /** A non-integer argument at a value call. */
    private static final String FRACTION_SOURCE = """
        export function main(): null {
          let f: (x: number) => int = int;
          let r: int = f(2.5);
          return null;
        }
        """;

    /** An integral argument outside signed32 (the E8004 range gate). */
    private static final String RANGE_SOURCE = """
        export function main(): null {
          let f: (x: number) => int = int;
          let r: int = f(2147483648.0);
          return null;
        }
        """;

    /** The direct arm's unchanged drive: the pinned NaN text at `int(n)`. */
    private static final String DIRECT_NAN_SOURCE = """
        export function main(): null {
          let z: number = 0.0;
          let n: number = z / z;
          let r: int = int(n);
          return null;
        }
        """;

    private record Fixture(Path root, CheckedProjectInput checkedProject,
                           ProjectInterfaceIndex index,
                           List<SemanticRequirementManifest> manifests,
                           HostDeclarationSurface surface,
                           Map<ModuleId, CanonicalModuleIdentity> identities) {
    }

    private static CompilerInvocation productionInvocation() {
        return CompilerProfileProvider.resolve(ReleaseConfiguration.CURRENT_RELEASE_STATE,
            ReleaseConfiguration.releaseCapabilityRegistry());
    }

    private static Fixture compileProject(Map<String, String> sources) throws Exception {
        Path root = Files.createTempDirectory("intrinsic-value-call");
        Path src = root.resolve("src");
        Files.createDirectories(src);
        for (Map.Entry<String, String> source : sources.entrySet()) {
            Path target = root.resolve(source.getKey());
            Files.createDirectories(target.getParent());
            Files.writeString(target, source.getValue(), StandardCharsets.UTF_8);
        }
        Path entry = src.resolve("app.deal").toAbsolutePath();
        Path output = root.resolve("out").toAbsolutePath();
        CompilationOrchestrator orchestrator = new CompilationOrchestrator(entry, output,
            false, false, false, false, Backend.LUAJIT, null,
            List.of(src.toAbsolutePath()), null, null, productionInvocation());
        boolean compiled = orchestrator.compile();
        CheckedProjectBuildResult built = orchestrator.checkedProject();
        RequirementManifestResult manifests = orchestrator.requirementManifests();
        if (!compiled || built == null || built.input() == null || built.index() == null
                || built.hasErrors() || manifests == null || manifests.manifests() == null
                || orchestrator.hostDeclarationSurface() == null) {
            deleteRecursively(root);
            fail("the fixture project did not build: "
                + (built == null ? "no checked project" : built.diagnostics()) + " / "
                + orchestrator.diagnostics());
            return null;
        }
        Map<ModuleId, CanonicalModuleIdentity> identities = new LinkedHashMap<>();
        for (ModuleId declaration : orchestrator.hostDeclarationSurface().moduleIds()) {
            identities.put(declaration,
                new CanonicalModuleIdentity.ExternalModule(declaration.path()));
        }
        return new Fixture(root, built.input(), built.index(), manifests.manifests(),
            orchestrator.hostDeclarationSurface(), identities);
    }

    private static SemanticLowerer.ProjectLoweringResult lower(Fixture fixture) {
        return SemanticLowerer.lowerProject(productionInvocation(),
            fixture.checkedProject(), fixture.index(), fixture.manifests(),
            fixture.surface(), fixture.identities(), Map.of(),
            BuiltinErrorDeclaration.synthesized(
                fixture.checkedProject().modules().get(0).ast().span()),
            List.of(IntrinsicKind.INT_CONVERT, IntrinsicKind.NUMBER_CONVERT), Set.of());
    }

    private static void deleteRecursively(Path path) {
        if (path == null) {
            return;
        }
        try {
            if (Files.exists(path)) {
                try (var walk = Files.walk(path)) {
                    walk.sorted(java.util.Comparator.reverseOrder()).forEach(entry -> {
                        try {
                            Files.deleteIfExists(entry);
                        } catch (java.io.IOException ignored) {
                            // best effort
                        }
                    });
                }
            }
        } catch (java.io.IOException ignored) {
            // best effort
        }
    }

    private static SemanticIrValidator.ComparisonFacts comparisonFacts(
            LoweredModuleUnit unit) {
        return new SemanticIrValidator.ComparisonFacts(unit.interfaceHash(),
            SemanticProfile.DEAL_V1_2_INT32,
            ReleaseConfiguration.releaseCapabilityRegistry().capabilityRegistryHash());
    }

    // =========================================================================
    // Op helpers
    // =========================================================================

    private static SemanticOp callOp(LoweredModuleUnit unit, Class<?> bindingShape) {
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CALL
                    && op.payload() instanceof KindPayload.CallPayload payload
                    && payload.callee() instanceof KindPayload.CallCallee.Static staticCallee
                    && bindingShape.isInstance(staticCallee.binding())) {
                return op;
            }
        }
        return null;
    }

    private static SemanticOp dynamicCall(LoweredModuleUnit unit) {
        for (SemanticOp op : unit.ops()) {
            if (op.payload() instanceof KindPayload.CallPayload call
                    && call.callee() instanceof KindPayload.CallCallee.Dynamic) {
                return op;
            }
        }
        return null;
    }

    private static int eventCount(SemanticRuntimeModel.ConsumerRun run, OpId op,
                                  SemanticRuntimeModel.Phase phase) {
        int count = 0;
        for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
            if (event.op().equals(op) && event.phase() == phase) {
                count++;
            }
        }
        return count;
    }

    private static String originText(SemanticOp op) {
        return op.origin().sourceId() + ":" + op.origin().span().startLine() + ":"
            + op.origin().span().startColumn();
    }

    private static void assertRule(Optional<CompilerDiagnostic> failure, String rule,
                                   String what) {
        check(failure.isPresent(), what + " fails the closed gate");
        if (failure.isEmpty()) {
            return;
        }
        String message = failure.get().message();
        check("E6005".equals(failure.get().code()), what + " is rejected with E6005");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the validator rule " + rule + "; got \"" + message + "\"");
    }

    // =========================================================================
    // 1. The nested static-callee shape admission
    // =========================================================================

    private static void testShapeAdmission() throws Exception {
        System.out.println("-- the closed nested static-callee shape admission: "
            + "CallCallee.Static(IntrinsicFunction) validates, the shape position keeps "
            + "its closed discipline, and the doctored nested payloads still fail --");
        Fixture fixture = compileProject(Map.of("src/app.deal", VALUE_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the value-position project lowers through the "
                + "one project entry: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp call = callOp(app, FunctionExecutionBinding.IntrinsicFunction.class);
            check(call != null, "the lowered unit carries the intrinsic static callee arm");
            if (call == null) {
                return;
            }
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            checkEq(CallMode.INDIRECT, payload.mode(),
                "the intrinsic static callee arm is the INDIRECT call mode");
            FunctionExecutionBinding.IntrinsicFunction intrinsic =
                (FunctionExecutionBinding.IntrinsicFunction)
                    ((KindPayload.CallCallee.Static) payload.callee()).binding();
            checkEq(IntrinsicKind.INT_CONVERT, intrinsic.kind(),
                "the recorded callee is the int conversion's registration");

            // The closed schema gate admits the unit: R-ENUM no longer rejects
            // the intrinsic callee shape (ISSUE-0679 retargets the landed pin
            // that forbade it).
            String text = SemanticIrValidator.toUnitText(app);
            Optional<CompilerDiagnostic> admission =
                SemanticIrValidator.validateText(text, comparisonFacts(app));
            check(admission.isEmpty(), "the unit carrying the intrinsic static callee "
                + "shape passes the closed schema gate: "
                + admission.map(CompilerDiagnostic::message).orElse("admission"));

            // The nested negatives: the closed shape position's own discipline.
            String declared = IntrinsicKind.INT_CONVERT.declaredSignature()
                .canonicalSpecText();
            String nested = "\"binding\":{\"descriptor\":\"" + declared
                + "\",\"intrinsicKind\":\"INT_CONVERT\",\"type\":\"intrinsicFunction\"}"
                + ",\"type\":\"static\"";
            check(text.contains(nested), "the unit text carries the nested intrinsic "
                + "callee shape position");
            if (!text.contains(nested)) {
                return;
            }
            String openKind = text.replace(nested,
                nested.replace("\"INT_CONVERT\"", "\"INT_OPEN\""));
            check(!openKind.equals(text), "the open-kind mutation targets the nested shape");
            assertRule(SemanticIrValidator.validateText(openKind, comparisonFacts(app)),
                "R-ENUM", "a nested intrinsic callee payload with an open kind");
            String absentKind = text.replace(nested,
                nested.replace(",\"intrinsicKind\":\"INT_CONVERT\"", ""));
            check(!absentKind.equals(text), "the absent-kind mutation targets the nested "
                + "shape");
            assertRule(SemanticIrValidator.validateText(absentKind, comparisonFacts(app)),
                "R-ENUM", "a nested intrinsic callee payload whose kind position is absent");
            String absentDescriptor = text.replace(nested,
                nested.replace("\"descriptor\":\"" + declared + "\",", ""));
            check(!absentDescriptor.equals(text), "the absent-descriptor mutation targets "
                + "the nested shape");
            assertRule(SemanticIrValidator.validateText(absentDescriptor,
                comparisonFacts(app)), "R-ENUM",
                "a nested intrinsic callee payload whose descriptor position is absent");

            // No other nested binding shape is newly admitted: the producer
            // rule's dynamic record stays outside the closed enumeration.
            String dynamicNested = text.replace(nested,
                "\"binding\":{\"descriptor\":\"" + declared
                    + "\",\"materializingBoundaryOpId\":null,"
                    + "\"type\":\"dynamicFunctionValue\"},\"type\":\"static\"");
            check(!dynamicNested.equals(text), "the dynamic-shape mutation targets the "
                + "nested shape");
            assertRule(SemanticIrValidator.validateText(dynamicNested,
                comparisonFacts(app)), "R-ENUM",
                "a nested dynamicFunctionValue callee payload");
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 2. The indirect arm's host cell family and the argument domain
    // =========================================================================

    private static void testIndirectArmAndArgumentDomain() throws Exception {
        System.out.println("-- the indirect arm's recorded host cell family: the declared "
            + "parameter cells own the argument domain and the single HOST_TO_DEAL + "
            + "HOST_SYNC_RETURN cell is run by the call op --");
        Fixture fixture = compileProject(Map.of("src/app.deal", VALUE_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the value-position project lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp call = callOp(app, FunctionExecutionBinding.IntrinsicFunction.class);
            if (call == null) {
                fail("the intrinsic static callee arm is missing");
                return;
            }
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            checkEq(1, payload.parameterBoundaryOpIds().size(),
                "the intrinsic's declared arity records one parameter cell");
            SemanticOp parameter = opOf(app, payload.parameterBoundaryOpIds().get(0));
            check(parameter != null, "the recorded parameter cell resolves");
            if (parameter != null) {
                KindPayload.BoundaryPayload boundary =
                    (KindPayload.BoundaryPayload) parameter.payload();
                checkEq(BoundaryKind.DEAL_TO_HOST, boundary.kind(),
                    "the parameter cell is the DEAL_TO_HOST family");
                checkEq(FailurePolicyId.HOST_PARAMETER, parameter.failurePolicy(),
                    "the parameter cell carries the pinned HOST_PARAMETER policy (the "
                        + "argument domain's E8010 row)");
                checkEq(IntrinsicKind.INT_CONVERT.declaredSignature().paramTypes().get(0),
                    boundary.descriptor(),
                    "the parameter cell checks the intrinsic's declared parameter "
                        + "descriptor");
            }
            SemanticOp returnCell = payload.returnBoundaryOpId() == null ? null
                : opOf(app, payload.returnBoundaryOpId());
            check(returnCell != null, "the intrinsic value call records its single return "
                + "cell");
            if (returnCell != null) {
                KindPayload.BoundaryPayload boundary =
                    (KindPayload.BoundaryPayload) returnCell.payload();
                checkEq(BoundaryKind.HOST_TO_DEAL, boundary.kind(),
                    "the return cell is the HOST_TO_DEAL family");
                checkEq(FailurePolicyId.HOST_SYNC_RETURN, returnCell.failurePolicy(),
                    "the return cell carries the pinned HOST_SYNC_RETURN policy");
                checkEq(IntrinsicKind.INT_CONVERT.declaredSignature().returnType(),
                    boundary.descriptor(),
                    "the return cell checks the intrinsic's declared return descriptor");
            }
            // The validator's indirect cell switch pins the family: the unit
            // passes the closed gate (R-BOUNDARY-TRIPLE included).
            check(SemanticIrValidator.validateText(SemanticIrValidator.toUnitText(app),
                    comparisonFacts(app)).isEmpty(),
                "the unit carrying the recorded host family passes the closed gate");

            // The argument domain is owned by the cells, and the conversion
            // never sees a null or a wrong kind: the recorded cell descriptor is
            // the non-nullable declared parameter.
            check(!(IntrinsicKind.INT_CONVERT.declaredSignature().paramTypes().get(0)
                    instanceof RuntimeDescriptor.Nullable),
                "the intrinsic value call's declared parameter is non-nullable (the "
                    + "recorded cell owns the null projection)");

            // The family is pinned, not merely admitted: a doctored unit that
            // records another cell family for the intrinsic's indirect call
            // fails the closed gate through the same resolved-binding switch.
            String callText = SemanticIrValidator.toUnitText(app);
            String parameterKind = "\"kind\":\"DEAL_TO_HOST\"";
            String returnKind = "\"kind\":\"HOST_TO_DEAL\"";
            check(callText.contains(parameterKind) && callText.contains(returnKind),
                "the unit text carries the recorded host cell family positions");
            if (callText.contains(parameterKind) && callText.contains(returnKind)) {
                assertRule(SemanticIrValidator.validateText(callText.replace(parameterKind,
                        "\"kind\":\"FUNCTION_PARAMETER\""), comparisonFacts(app)),
                    "R-BOUNDARY-TRIPLE",
                    "an intrinsic indirect call recording a FUNCTION_PARAMETER cell");
                assertRule(SemanticIrValidator.validateText(callText.replace(returnKind,
                        "\"kind\":\"FUNCTION_RETURN\""), comparisonFacts(app)),
                    "R-BOUNDARY-TRIPLE",
                    "an intrinsic indirect call recording a FUNCTION_RETURN cell");
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static SemanticOp opOf(LoweredModuleUnit unit, OpId id) {
        for (SemanticOp op : unit.ops()) {
            if (op.opId().equals(id)) {
                return op;
            }
        }
        return null;
    }

    // =========================================================================
    // 3. The ladder with the invoking op's context and kind
    // =========================================================================

    private static void testValueCallDrives() throws Exception {
        System.out.println("-- the value call on all three consumers: the conversion runs "
            + "with the invoking CALL op's context, the recorded return cell runs exactly "
            + "once, and a valid input converts exactly --");
        Fixture fixture = compileProject(Map.of("src/app.deal", VALUE_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the value-position project lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = callOp(app, FunctionExecutionBinding.IntrinsicFunction.class);
            if (call == null) {
                fail("the intrinsic static callee arm is missing");
                return;
            }
            OpId returnCell = ((KindPayload.CallPayload) call.payload())
                .returnBoundaryOpId();

            // The emitted static arm: the one ladder with the invoking CALL op's
            // context and kind, the host cell family, and no fail-closed default.
            String lua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            check(lua.contains("local function __intConv(v, evKind, kind, opKey, digest, "
                    + "parent, origin)"),
                "the LuaJIT ladder helper carries the invoking op's kind parameter");
            check(lua.contains("__resT = __intConv(__hbT[1], \"CALL\", \"number\""),
                "the LuaJIT static arm runs the ladder with the CALL op's kind label");
            check(lua.contains("if v.__it ~= nil then return \"HOST\" end"),
                "the LuaJIT class chain recognizes the memoized intrinsic carrier");
            String jvm = JvmSemanticEmitter.emitProject(project, result.tables(),
                result.registries()).source();
            check(jvm.contains("JvmRuntime.intConv(__ip_"),
                "the JVM static arm runs the ladder over the recorded parameter cell");
            check(jvm.contains(", \"CALL\", "),
                "the JVM static arm passes the invoking CALL op's kind label to the "
                    + "ladder");

            Path workspace = Files.createTempDirectory("intrinsic-value-call-drive");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "intrinsic value call", List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer value-call drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), "all three consumers produced a run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the value call started once");
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the value call published the converted value");
                    checkEq(1, eventCount(run, returnCell,
                            SemanticRuntimeModel.Phase.START),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell started once");
                    checkEq(1, eventCount(run, returnCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell admitted the "
                            + "converted value");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testLadderFailures() throws Exception {
        System.out.println("-- the reachable ladder rows at the call origin with the "
            + "invoking CALL op's kind: NaN, infinity, a non-integer, and the E8004 range "
            + "gate, identically on the oracle and both production artifacts --");
        ladderFailureDrive(NAN_SOURCE, "int(NaN) at a value call", "E8001",
            "expected int, got NaN");
        ladderFailureDrive(INFINITY_SOURCE, "int(infinity) at a value call", "E8001",
            "expected int, got infinity");
        ladderFailureDrive(FRACTION_SOURCE, "int(2.5) at a value call", "E8001",
            "expected int, got non-integer number");
        ladderFailureDrive(RANGE_SOURCE, "int(2147483648.0) at a value call", "E8004",
            "int out of safe range");
    }

    private static void ladderFailureDrive(String source, String what, String code,
                                            String message) throws Exception {
        Fixture fixture = compileProject(Map.of("src/app.deal", source));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, what + " lowers: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp call = callOp(app, FunctionExecutionBinding.IntrinsicFunction.class);
            check(call != null, what + " produces the intrinsic static callee arm");
            if (call == null) {
                return;
            }
            String origin = originText(call);
            Path workspace = Files.createTempDirectory("intrinsic-value-failure");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure(what, List.of(),
                            code, origin),
                        workspace);
                check(verdict.pass(), what + ": the three-consumer failure drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), what + ": three consumer runs");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && code.equals(failure.error().code())
                            && message.equals(failure.error().message())
                            && origin.equals(failure.error().origin()),
                        run.consumer() + ": the pinned text and the call origin: "
                            + run.terminal());
                    boolean sawCallFailure = false;
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.op().equals(call.opId())
                                && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                            sawCallFailure = true;
                            checkEq(SemanticOpKind.CALL, event.kind(), run.consumer()
                                + ": the failure event carries the invoking CALL op's "
                                + "own kind");
                        }
                    }
                    check(sawCallFailure, run.consumer() + ": the CALL op's FAILURE "
                        + "terminal is published");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    private static void testDirectArmUnchanged() throws Exception {
        System.out.println("-- the direct INTRINSIC_CALL arm keeps its own kind label and "
            + "its pinned text --");
        Fixture fixture = compileProject(Map.of("src/app.deal", DIRECT_NAN_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the direct-arm project lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit app = result.project().modules().get(APP);
            SemanticOp direct = null;
            for (SemanticOp op : app.ops()) {
                if (op.kind() == SemanticOpKind.INTRINSIC_CALL) {
                    direct = op;
                }
            }
            check(direct != null, "the direct-arm project carries the INTRINSIC_CALL op");
            if (direct == null) {
                return;
            }
            String origin = originText(direct);
            Path workspace = Files.createTempDirectory("intrinsic-direct-arm");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.failure("direct arm",
                            List.of(), "E8001", origin),
                        workspace);
                check(verdict.pass(), "the direct arm's three-consumer drive passes: "
                    + verdict.report());
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    check(run.terminal()
                            instanceof SemanticRuntimeModel.Terminal.DealFailure failure
                            && "expected int, got NaN".equals(failure.error().message())
                            && origin.equals(failure.error().origin()),
                        run.consumer() + ": the direct arm keeps its pinned text and its "
                            + "own origin: " + run.terminal());
                    boolean sawDirectFailure = false;
                    for (SemanticRuntimeModel.TraceEvent event : run.trace()) {
                        if (event.op().equals(direct.opId())
                                && event.phase() == SemanticRuntimeModel.Phase.FAILURE) {
                            sawDirectFailure = true;
                            checkEq(SemanticOpKind.INTRINSIC_CALL, event.kind(),
                                run.consumer() + ": the direct arm's failure event keeps "
                                    + "its own INTRINSIC_CALL kind");
                        }
                    }
                    check(sawDirectFailure, run.consumer() + ": the direct arm's FAILURE "
                        + "terminal is published");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 4. The dynamic arm
    // =========================================================================

    private static void testDynamicArmDrive() throws Exception {
        System.out.println("-- the dynamic arm: a function-typed parameter callee holding "
            + "the intrinsic resolves the HOST class from its own tag and runs the same "
            + "conversion with the call op's context --");
        Fixture fixture = compileProject(Map.of("src/app.deal", CALLBACK_SOURCE));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, "the callback project lowers: "
                + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            ExecutableLoweredProject project = result.project();
            LoweredModuleUnit app = project.modules().get(APP);
            SemanticOp call = dynamicCall(app);
            check(call != null, "the callback project produces the dynamic callee shape");
            if (call == null) {
                return;
            }
            KindPayload.CallPayload payload = (KindPayload.CallPayload) call.payload();
            // The dynamic arm's recorded parameter cells are the class-independent
            // FUNCTION_PARAMETER family (the descriptor-kind rule).
            checkEq(1, payload.parameterBoundaryOpIds().size(),
                "the dynamic call records its declared parameter cell");
            SemanticOp parameter = opOf(app, payload.parameterBoundaryOpIds().get(0));
            check(parameter != null && parameter.payload()
                    instanceof KindPayload.BoundaryPayload boundary
                    && boundary.kind() == BoundaryKind.FUNCTION_PARAMETER
                    && parameter.failurePolicy() != FailurePolicyId.HOST_PARAMETER,
                "the dynamic arm's parameter cell is the class-independent "
                    + "FUNCTION_PARAMETER family under the descriptor-kind policy (not the "
                    + "static arm's host family)");
            OpId hostCell = payload.dynamicReturnBoundary().hostBoundaryOpId();

            String lua = LuaSemanticEmitter.emitProject(project, result.tables(),
                result.registries());
            check(lua.contains("if __dynC.__it == \"INT_CONVERT\" then")
                    && lua.contains("if __dynC.__it == \"NUMBER_CONVERT\" then"),
                "the LuaJIT HOST row resolves the intrinsic's own kind tag");
            check(lua.contains("__resT = __numConv("),
                "the LuaJIT HOST row runs the number conversion ladder for the callback");
            String jvm = JvmSemanticEmitter.emitProject(project, result.tables(),
                result.registries()).source();
            check(jvm.contains("instanceof JvmRuntime.Intrinsic __iv"),
                "the JVM HOST row admits the intrinsic carrier additively");
            check(jvm.contains("JvmRuntime.numConv("),
                "the JVM HOST row runs the number conversion ladder for the callback");

            Path workspace = Files.createTempDirectory("intrinsic-callback-drive");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(project, result.tables(),
                        result.registries(),
                        SemanticDifferentialHarness.Expectation.success(
                            "intrinsic callback", List.of(), "null"),
                        workspace);
                check(verdict.pass(), "the three-consumer callback drive passes: "
                    + verdict.report());
                checkEq(3, verdict.runs().size(), "all three consumers produced a run");
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the dynamic call published the converted value");
                    checkEq(1, eventCount(run, hostCell,
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the recorded HOST_TO_DEAL cell admitted the "
                            + "converted value");
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // 5. The corpus fixture drives
    // =========================================================================

    private static void testCorpusFixtureDrives() throws Exception {
        System.out.println("-- the corpus primitives: the fixture text verbatim in a "
            + "library module, driven through the production artifacts --");
        corpusFixtureDrive("intrinsic-as-function-value",
            "test_intrinsic_as_function_value", "int", "3");
        corpusFixtureDrive("intrinsic-as-callback",
            "test_intrinsic_as_callback", "number", "7.0");
    }

    /**
     * The fixture's code with the lane harness's {@code // @…} directive header
     * removed: the directives are the conformance lane's metadata (the lane's
     * lexer hands its directive events to the parser), so the drive compiles
     * exactly the fixture's program text. The corpus's trailing no-op
     * {@code main} entry shim is removed by the caller before the fixture is
     * placed in a library module: the shim is the corpus lane's entry, and this
     * drive supplies its own entry which invokes the fixture's test export.
     */
    private static String fixtureCode(String source) {
        StringBuilder out = new StringBuilder();
        for (String line : source.lines().toList()) {
            if (line.startsWith("// @")) {
                continue;
            }
            out.append(line).append('\n');
        }
        return out.toString();
    }

    private static void corpusFixtureDrive(String fixtureName, String exportName,
                                           String resultType, String expectedAtom)
            throws Exception {
        Path fixtureFile = Path.of("test", "conformance", "backend-runtime", "functions",
            fixtureName + ".deal");
        check(Files.exists(fixtureFile), fixtureName + " is the corpus fixture");
        if (!Files.exists(fixtureFile)) {
            return;
        }
        String rawFixture = Files.readString(fixtureFile, StandardCharsets.UTF_8);
        String fixtureSource = fixtureCode(rawFixture);
        String entryShim = "export function main(): null {\n  return null;\n}\n";
        String withoutShim = fixtureSource.replace(entryShim, "");
        check(!withoutShim.equals(fixtureSource), fixtureName + ": the corpus entry shim is "
            + "the drive's own entry");
        fixtureSource = withoutShim;
        String driver = """
            import * as lib from "./lib"

            export function main(): null {
              let r: %s = lib.%s()
              if (r !== %s) {
                throw { code: "TEST_FAIL", message: "corpus fixture drive" }
              }
              return null
            }
            """.formatted(resultType, exportName, expectedAtom);
        Fixture fixture = compileProject(Map.of(
            "src/lib.deal", fixtureSource, "src/app.deal", driver));
        if (fixture == null) {
            return;
        }
        try {
            SemanticLowerer.ProjectLoweringResult result = lower(fixture);
            check(result.project() != null, fixtureName + " lowers with the fixture text "
                + "verbatim: " + result.diagnostics());
            if (result.project() == null) {
                return;
            }
            LoweredModuleUnit lib = result.project().modules()
                .get(new ModuleId("lib"));
            check(lib != null, fixtureName + ": the fixture module is part of the closure");
            if (lib == null) {
                return;
            }
            SemanticOp call = callOp(lib, FunctionExecutionBinding.IntrinsicFunction.class);
            OpId selectedCell = null;
            if (call != null) {
                checkEq(IntrinsicKind.INT_CONVERT,
                    ((FunctionExecutionBinding.IntrinsicFunction)
                        ((KindPayload.CallCallee.Static) ((KindPayload.CallPayload)
                            call.payload()).callee()).binding()).kind(),
                    fixtureName + ": the static indirect arm resolves the int conversion");
                selectedCell = ((KindPayload.CallPayload) call.payload())
                    .returnBoundaryOpId();
            } else {
                SemanticOp dynamic = dynamicCall(lib);
                check(dynamic != null, fixtureName + ": the callback fixture produces the "
                    + "dynamic callee arm");
                if (dynamic == null) {
                    return;
                }
                call = dynamic;
                selectedCell = ((KindPayload.CallPayload) dynamic.payload())
                    .dynamicReturnBoundary().hostBoundaryOpId();
            }
            check(selectedCell != null, fixtureName + ": the recorded host return cell is "
                + "present");
            Path workspace = Files.createTempDirectory("intrinsic-fixture-drive");
            try {
                SemanticDifferentialHarness.Verdict verdict =
                    SemanticDifferentialHarness.runProject(result.project(),
                        result.tables(), result.registries(),
                        SemanticDifferentialHarness.Expectation.success(fixtureName,
                            List.of(), "null"),
                        workspace);
                check(verdict.pass(), fixtureName + ": the three-consumer fixture drive "
                    + "passes: " + verdict.report());
                for (SemanticRuntimeModel.ConsumerRun run : verdict.runs()) {
                    checkEq(1, eventCount(run, call.opId(),
                            SemanticRuntimeModel.Phase.SUCCESS),
                        run.consumer() + ": the fixture's intrinsic call executed its class "
                            + "path");
                    if (selectedCell != null) {
                        checkEq(1, eventCount(run, selectedCell,
                                SemanticRuntimeModel.Phase.SUCCESS),
                            run.consumer() + ": the fixture's selected host cell ran once");
                    }
                }
            } finally {
                deleteRecursively(workspace);
            }
        } finally {
            deleteRecursively(fixture.root());
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) throws Exception {
        System.out.println("=== Conversion Intrinsic Value Call Tests (ISSUE-0679) ===\n");

        testShapeAdmission();
        testIndirectArmAndArgumentDomain();
        testValueCallDrives();
        testLadderFailures();
        testDirectArmUnchanged();
        testDynamicArmDrive();
        testCorpusFixtureDrives();

        System.out.println("\nIntrinsic value call: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
