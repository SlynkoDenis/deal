package deal.test;

import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.semantic.DescriptorService;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.ValueId;
import deal.types.Type;
import deal.test.IdentityTestFixtures;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The wiki-Verification-4 full-table corpus (ISSUE-0366, ISSUE-0233 D5):
 * one passing validated unit per row of the closed boundary-assignment
 * table — the descriptor-kind-rule cells (a), the pinned host-direction
 * cells (b), the {@code CALL(INDIRECT)}/{@code ASYNC_START}→
 * {@code AdapterBinding} rows for every source kind (c), the
 * {@code CALLBACK_INVOKE} rows (d), the core array element cells (e), the
 * external/stdlib cells (f), the {@code EXTERNAL_ENTRY} row sync and
 * async (g), the {@code ASYNC_START} rows (h), the {@code AWAIT}
 * completion cell (i), the zero-boundary shapes (j), and the JSON
 * exception cells (k) — plus one out-of-table negative per row family and
 * the validator/executor tie invariant in both directions.
 *
 * <p>The foundation validator stays the table's validation form
 * ({@link SemanticIrValidator} R-BOUNDARY-TRIPLE, preserved — this
 * corpus changes no validator production code); {@link BoundaryExecutor}
 * is its execution form. The tie is pinned as an invariant: every
 * validator-accepted cell of a positive row executes through
 * {@link BoundaryExecutor#check} with a view matching the declared
 * descriptor and yields the row's pinned Pass projection (or the pinned
 * failure projection of the JSON_TO_ERROR/array-boundary arms), every
 * out-of-table triple is rejected by the validator with the pinned
 * first-failure rule named in the E6005 detail, and the executor refuses
 * the 13 non-{@code BOUNDARY} policies fail closed.</p>
 *
 * <p>Every corpus fixture is a synthetic typed construction
 * ({@link KindPayload}/{@link SemanticOp}); every descriptor is produced
 * through {@link DescriptorService#describe(Type)} — never hand-built
 * {@code RuntimeDescriptor} values. Every positive and negative runs
 * through {@link SemanticIrValidator#validate(LoweredModuleUnit,
 * SemanticIrValidator.ComparisonFacts)} on the typed surface (projects
 * for the cross-unit shared-body rows); the raw-name reserved fixtures
 * run through {@link SemanticIrValidator#validateText(String,
 * SemanticIrValidator.ComparisonFacts)} — the pinned invalid-IR
 * injection route. Every positive unit's {@code BOUNDARY} payload carries
 * a non-empty {@code RuntimeValidation} realization inspected directly
 * from the validated Semantic IR.</p>
 */
public class BoundaryTableCorpusTest {

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

    private static void expectDefect(Runnable runnable, String what) {
        try {
            runnable.run();
            fail("expected BoundaryExecutor.Defect for " + what + ", but no exception was raised");
        } catch (BoundaryExecutor.Defect expected) {
            passed++;
        } catch (Throwable other) {
            fail("expected BoundaryExecutor.Defect for " + what + ", got "
                + other.getClass().getSimpleName() + ": " + other.getMessage());
        }
    }

    // =========================================================================
    // Shared synthetic fixtures (descriptors produced through DescriptorService)
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("mod.a");
    private static final ModuleId MOD_B = new ModuleId("mod.b");
    private static final ModuleId MOD_HOST = new ModuleId("host.m");
    private static final String IFACE = "interface-digest-1";
    private static final String REGISTRY = "capability-registry-hash-1";
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(IFACE, SemanticProfile.DEAL_V1_2_INT32, REGISTRY);
    private static final String LCH =
        LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY);

    // Every corpus descriptor comes from the single Type→descriptor
    // producer (the pinned D1 producer-singularity seam).
    private static final RuntimeDescriptor STRING = DescriptorService.describe(Type.String.INSTANCE);
    private static final RuntimeDescriptor INT = DescriptorService.describe(Type.Int.INSTANCE);
    private static final RuntimeDescriptor BOOLEAN = DescriptorService.describe(Type.Boolean.INSTANCE);
    private static final RuntimeDescriptor NUMBER = DescriptorService.describe(Type.Number.INSTANCE);
    private static final RuntimeDescriptor TABLE_D = DescriptorService.describe(Type.Table.INSTANCE);
    private static final RuntimeDescriptor NULL_D = DescriptorService.describe(Type.Null.INSTANCE);
    private static final RuntimeDescriptor NULLABLE_STRING =
        DescriptorService.describe(new Type.Nullable(Type.String.INSTANCE));
    private static final RuntimeDescriptor ARRAY_INT =
        DescriptorService.describe(new Type.Array(Type.Int.INSTANCE));
    private static final RuntimeDescriptor USER =
        DescriptorService.describe(IdentityTestFixtures.classType("User", "src/app"));
    private static final RuntimeDescriptor.Func F_II = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.Int.INSTANCE));
    private static final RuntimeDescriptor.Func F_IIS = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
            Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func F_IS = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE), Type.String.INSTANCE));
    private static final RuntimeDescriptor.Func F_IIS_ASYNC = (RuntimeDescriptor.Func)
        DescriptorService.describe(new Type.Func(List.of(Type.Int.INSTANCE, Type.Int.INSTANCE),
            Type.String.INSTANCE, true));

    private static int nextOp = 1;
    private static int nextVal = 1;

    private static OpId nextOpId() {
        return new OpId(MOD, nextOp++);
    }

    private static OpId nextOpId(ModuleId module) {
        return new OpId(module, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static SourceOrigin origin(OpId parent) {
        return new SourceOrigin("test.deal", SourceSpan.synthetic("test.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), parent);
    }

    private static OperationContractSnapshot contractFor(SemanticOpKind kind, KindPayload payload,
            OpResultType resultType, List<RuntimeDescriptor> operandTypes,
            FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector() : null;
        return new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind, resultType,
            operandTypes, selector, payload, policy, List.of(), digest);
    }

    private static SemanticOp opWith(OpId id, SemanticOpKind kind, KindPayload payload,
            SemanticValue result, OpResultType resultType, FailurePolicyId policy, OpId parent) {
        OperationContractSnapshot contract =
            contractFor(kind, payload, resultType, List.of(), policy, "placeholder");
        String digest = ContractSnapshotCanonicalizer.digest(contract);
        contract = contractFor(kind, payload, resultType, List.of(), policy, digest);
        return new SemanticOp(id, kind, origin(parent), result, resultType, List.of(), List.of(),
            payload, policy, contract);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy, OpId parent) {
        return opWith(nextOpId(), kind, payload, result, resultType, policy, parent);
    }

    private static SemanticOp boundaryWith(OpId id, BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent) {
        return opWith(id, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(kind, descriptor, nextValue(),
                new BoundaryRealization.RuntimeValidation("check-" + id.id())),
            null, null, policy, parent);
    }

    private static SemanticOp boundary(BoundaryKind kind, RuntimeDescriptor descriptor,
            FailurePolicyId policy, OpId parent) {
        return boundaryWith(nextOpId(), kind, descriptor, policy, parent);
    }

    private static LoweredModuleUnit unit(ModuleId module, Set<SemanticCapability> caps,
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, module, IFACE, LCH, caps, Map.of(), Map.of(),
            Map.of(), new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            bindings, ops);
    }

    private static LoweredModuleUnit unit(Map<FunctionAllocationIdentity, FunctionExecutionBinding> bindings,
            List<SemanticOp> ops) {
        return unit(MOD, Set.of(), bindings, ops);
    }

    private static LoweredModuleUnit unit(List<SemanticOp> ops) {
        return unit(MOD, Set.of(), Map.of(), ops);
    }

    private static ExternalModuleInterface interfaceOf(ModuleId module) {
        return new ExternalModuleInterface(module, ExternalModuleKind.IMPLEMENTATION,
            List.of(), List.of(), List.of(), InitializationMode.ONCE_AFTER_DEPENDENCIES);
    }

    private static ExecutableLoweredProject projectOf(List<LoweredModuleUnit> units, ModuleId entry) {
        Map<ModuleId, ExternalModuleInterface> indexEntries = new LinkedHashMap<>();
        Map<ModuleId, LoweredModuleUnit> modules = new LinkedHashMap<>();
        for (LoweredModuleUnit unit : units) {
            indexEntries.put(unit.moduleId(), interfaceOf(unit.moduleId()));
            modules.put(unit.moduleId(), unit);
        }
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
            indexEntries);
        return new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32, index, modules, entry);
    }

    // =========================================================================
    // Corpus row model (positives) and executor-tie arms
    // =========================================================================

    /** One executor arm: a view, a context, and the pinned expected outcome. */
    private record ExecArm(BoundaryValueView view, BoundaryContext context,
                           ExecExpectation expected) {
    }

    private sealed interface ExecExpectation permits ExecPass, ExecFail {
    }

    /** An expected Pass; {@code sameInstance} pins "the same semantic value" (never copied). */
    private record ExecPass(BoundaryValueView value, boolean sameInstance)
        implements ExecExpectation {
    }

    /** An expected structured failure (registry-row projection fields). */
    private record ExecFail(DiagnosticCode code, String message, String expected, String actual,
                            Map<String, String> metadata) implements ExecExpectation {
    }

    /**
     * One positive corpus row: a named validated unit (or a cross-unit
     * project) plus optional explicit executor arms; boundary ops without
     * an explicit arm run the default matching-view Pass arm.
     */
    private record Row(String name, String family, List<LoweredModuleUnit> units, ModuleId entry,
                       Map<OpId, List<ExecArm>> arms) {

        Row {
            units = List.copyOf(units);
            arms = arms == null ? Map.of() : arms;
        }
    }

    private static Row single(String name, String family, LoweredModuleUnit unit) {
        return new Row(name, family, List.of(unit), null, Map.of());
    }

    private static Row single(String name, String family, LoweredModuleUnit unit,
                              Map<OpId, List<ExecArm>> arms) {
        return new Row(name, family, List.of(unit), null, arms);
    }

    private static Row projectRow(String name, String family, List<LoweredModuleUnit> units,
                                  ModuleId entry) {
        return new Row(name, family, units, entry, Map.of());
    }

    private static Map<OpId, List<ExecArm>> armsOf(OpId boundary, ExecArm... arms) {
        return Map.of(boundary, List.of(arms));
    }

    /** The default matching view for a declared descriptor (the tie's Pass arm). */
    private static BoundaryValueView matchingView(RuntimeDescriptor descriptor) {
        return switch (descriptor) {
            case RuntimeDescriptor.Null ignored -> BoundaryValueView.nullView();
            case RuntimeDescriptor.Boolean ignored -> BoundaryValueView.of(ActualKind.BOOLEAN);
            case RuntimeDescriptor.Int ignored -> BoundaryValueView.ofInt(7);
            case RuntimeDescriptor.Number ignored -> BoundaryValueView.ofNumber(1.5);
            case RuntimeDescriptor.String ignored -> BoundaryValueView.of(ActualKind.STRING);
            case RuntimeDescriptor.Table ignored -> BoundaryValueView.of(ActualKind.TABLE);
            case RuntimeDescriptor.Bytes ignored -> {
                // Bytes boundaries are backend-owned (ISSUE-0158): the
                // closed boundary-assignment table has no bytes cell and
                // no matching view can be constructed — no corpus row
                // carries a bytes descriptor, so this arm is a
                // fail-closed pin, never production-reachable.
                fail("no matching view exists for the bytes descriptor: bytes "
                    + "boundaries are backend-owned (ISSUE-0158) and the closed "
                    + "boundary-assignment table has no bytes cell");
                yield BoundaryValueView.nullView();
            }
            case RuntimeDescriptor.Class cls -> BoundaryValueView.ofClass(cls.classId().text());
            case RuntimeDescriptor.Array array ->
                BoundaryValueView.ofArray(matchingView(array.element()));
            case RuntimeDescriptor.Nullable ignored -> BoundaryValueView.nullView();
            case RuntimeDescriptor.Func func -> BoundaryValueView.ofFunction(func);
        };
    }

    /** The default valid context for a context-bearing policy. */
    private static BoundaryContext defaultContext(FailurePolicyId policy) {
        return switch (policy) {
            case HOST_PARAMETER -> BoundaryContext.parameter(1);
            case ARRAY_ELEMENT_DESCRIPTOR -> BoundaryContext.element(1);
            case ARRAY_READ_INDEX_THEN_DESCRIPTOR -> BoundaryContext.arrayIndex(0);
            case ARRAY_WRITE_BOUNDS_THEN_ELEMENT, ARRAY_DELETE_BOUNDS ->
                BoundaryContext.writeBounds(1, 3);
            case JSON_TO_ERROR -> BoundaryContext.jsonField("f");
            default -> BoundaryContext.none();
        };
    }

    // =========================================================================
    // Assertion helpers (the exact empty/E6005 surface, first failing rule named)
    // =========================================================================

    private static void assertPass(Optional<CompilerDiagnostic> diagnostic, String what) {
        check(diagnostic.isEmpty(), what + " passes validation"
            + (diagnostic.isPresent() ? ": " + diagnostic.get().message() : ""));
    }

    private static void assertE6005(Optional<CompilerDiagnostic> diagnostic, String rule,
            String... contains) {
        check(diagnostic.isPresent(), rule + " is rejected with E6005");
        if (diagnostic.isEmpty()) {
            return;
        }
        CompilerDiagnostic d = diagnostic.get();
        check("E6005".equals(d.code()), rule + " diagnostic code is E6005");
        check(d.diagnosticCode() == DiagnosticCode.E6005, rule + " diagnosticCode is E6005");
        check(DiagnosticCode.E6005.phase() == DiagnosticCode.Phase.BACKEND_LOWERING,
            rule + " phase is BACKEND_LOWERING");
        check("error".equals(d.severity()), rule + " severity is error");
        String message = d.message();
        check(message.startsWith("Common semantic lowering failed"),
            rule + " message instantiates the registry-owned E6005 template");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            rule + " is named as the validator rule (exactly one rule per fixture); got \""
                + message + "\"");
        check(message.contains("deal.semantic-ir/1") && message.contains("mod"),
            rule + " message carries the detail fields");
        for (String c : contains) {
            check(message.contains(c), rule + " message contains \"" + c + "\"; got \"" + message + "\"");
        }
    }

    private static void assertExec(BoundaryOutcome outcome, ExecExpectation expected, String what) {
        switch (expected) {
            case ExecPass passExpectation -> {
                if (outcome instanceof BoundaryOutcome.Pass pass) {
                    if (passExpectation.sameInstance()) {
                        check(pass.value() == passExpectation.value(),
                            what + ": Pass publishes the same semantic value (same view "
                                + "instance, never copied)");
                    } else {
                        check(pass.value().kind() == passExpectation.value().kind(),
                            what + ": Pass publishes a view of kind "
                                + passExpectation.value().kind() + ", got " + pass.value().kind());
                    }
                    passed++;
                } else {
                    fail(what + ": expected Pass, got " + outcome);
                }
            }
            case ExecFail failExpectation -> {
                if (!(outcome instanceof BoundaryOutcome.Fail failOutcome)) {
                    fail(what + ": expected Fail, got " + outcome);
                    return;
                }
                BoundaryFailure failure = failOutcome.failure();
                check(failure.code() == failExpectation.code(),
                    what + " code: expected " + failExpectation.code() + ", got " + failure.code());
                check(failExpectation.message().equals(failure.message()),
                    what + " message: expected [" + failExpectation.message() + "], got ["
                        + failure.message() + "]");
                check(Objects.equals(failExpectation.expected(), failure.expected()),
                    what + " expected field: expected [" + failExpectation.expected() + "], got ["
                        + failure.expected() + "]");
                check(Objects.equals(failExpectation.actual(), failure.actual()),
                    what + " actual field: expected [" + failExpectation.actual() + "], got ["
                        + failure.actual() + "]");
                check(failExpectation.metadata().equals(failure.metadata()),
                    what + " metadata: expected " + failExpectation.metadata() + ", got "
                        + failure.metadata());
                check(failure.cause() == null,
                    what + " cause: expected null, got " + failure.cause());
                passed++;
            }
        }
    }

    // =========================================================================
    // 1. Preservation pins: the closed 14 rules and the closed enums stay exact
    // =========================================================================

    private static boolean enumMember(Class<? extends Enum<?>> closed, String name) {
        for (Enum<?> value : closed.getEnumConstants()) {
            if (value.name().equals(name)) {
                return true;
            }
        }
        return false;
    }

    static void testPreservationPins() {
        System.out.println("-- Preservation pins: 14 rules, closed enums, reserved names --");

        check(SemanticIrValidator.RULES.equals(List.of(
                "R-COVERAGE", "R-ENUM", "R-CAPABILITY", "R-POLICY-KIND", "R-BOUNDARY-TRIPLE",
                "R-ELIDED-PLACEMENT", "R-FUNCTION-BINDING", "R-EXTERNAL-ENTRY", "R-ALIAS-CYCLE",
                "R-TOKEN-REUSE", "R-PRIVATE-STEP", "R-RESERVED-NAME", "R-DIGEST", "R-PROFILE")),
            "SemanticIrValidator.RULES is exactly the closed 14-condition list in S6 order; got "
                + SemanticIrValidator.RULES);
        check(SemanticIrValidator.RULES.size() == 14, "exactly 14 rules, nothing more or less");

        List<String> boundaryNames = new ArrayList<>();
        for (BoundaryKind kind : BoundaryKind.values()) {
            boundaryNames.add(kind.name());
        }
        check(boundaryNames.equals(List.of(
                "VARIABLE_DECLARATION", "VARIABLE_ASSIGNMENT", "CLASS_FIELD_ASSIGNMENT",
                "ARRAY_ELEMENT_ASSIGNMENT", "BYTE_ELEMENT_ASSIGNMENT", "ARRAY_ELEMENT_READ",
                "BYTE_ELEMENT_READ", "ARRAY_ELEMENT_DELETE",
                "ARRAY_LITERAL_ELEMENT", "FUNCTION_PARAMETER", "FUNCTION_RETURN",
                "ASYNC_COMPLETION", "CLASS_LITERAL_FIELD", "CLASS_DEFAULT_FIELD",
                "UNTYPED_CLASS_INPUT", "OPTIONAL_FIELD_READ", "CONTEXTUAL_TABLE_READ",
                "IMPORTED_MEMBER_READ", "MODULE_EXPORT", "HOST_TO_DEAL", "DEAL_TO_HOST",
                "STDLIB_PARAMETER", "STDLIB_RETURN", "EXTERNAL_PARAMETER", "EXTERNAL_RETURN",
                "JSON_FROM_FIELD", "JSON_TO_FIELD")),
            "BoundaryKind keeps the 27 closed values in the pinned order; got " + boundaryNames);
        check(BoundaryKind.values().length == 27,
            "exactly 27 BoundaryKind values, got " + BoundaryKind.values().length);
        check(BoundaryKind.RESERVED_NAMES.equals(List.of(
                "C_FFI_TO_DEAL", "DEAL_TO_C_FFI")),
            "BoundaryKind.RESERVED_NAMES is exactly the two pinned reserved names");
        for (String reserved : BoundaryKind.RESERVED_NAMES) {
            check(!enumMember(BoundaryKind.class, reserved),
                reserved + " stays a reserved name, never an enum member");
            check(BoundaryKind.isReservedName(reserved),
                "isReservedName(\"" + reserved + "\") is true");
        }

        List<String> policyNames = new ArrayList<>();
        for (FailurePolicyId policy : FailurePolicyId.values()) {
            policyNames.add(policy.name());
        }
        check(policyNames.equals(List.of(
                "NO_DEAL_FAILURE", "TYPE_DESCRIPTOR", "INT32_RESULT",
                "INT32_DIVISOR_THEN_RESULT", "INT32_EXPONENT_THEN_RESULT", "INT_CONVERSION",
                "NUMBER_CONVERSION", "ARRAY_ELEMENT_DESCRIPTOR",
                "ARRAY_READ_INDEX_THEN_DESCRIPTOR", "ARRAY_WRITE_BOUNDS_THEN_ELEMENT",
                "ARRAY_DELETE_BOUNDS", "BYTES_ALLOCATE", "BYTES_READ", "BYTES_WRITE",
                "FUNCTION_SIGNATURE", "HOST_PARAMETER",
                "HOST_SYNC_RETURN", "ASYNC_COMPLETION", "ASYNC_OPERATION_HANDLE", "HOST_LOAD",
                "CLASS_CONSTRUCTION", "JSON_PARSE_SYNTAX", "JSON_FROM_NULL", "JSON_TO_ERROR",
                "SQRT_NEGATIVE", "THROW_TRANSFER", "INFRASTRUCTURE_ONLY")),
            "FailurePolicyId keeps the 27 closed values in the pinned order; got " + policyNames);
        check(FailurePolicyId.values().length == 27,
            "exactly 27 FailurePolicyId values, got " + FailurePolicyId.values().length);
        check(FailurePolicyId.RESERVED_NAMES.equals(List.of(
                "EXTERNAL_PARAMETER", "EXTERNAL_RETURN", "STDLIB_PARAMETER", "STDLIB_RETURN")),
            "FailurePolicyId.RESERVED_NAMES is exactly the four pinned reserved names");
        for (String reserved : FailurePolicyId.RESERVED_NAMES) {
            check(!enumMember(FailurePolicyId.class, reserved),
                reserved + " stays a reserved policy name, never an enum member");
            check(FailurePolicyId.isReservedName(reserved),
                "isReservedName(\"" + reserved + "\") is true");
        }

        // The reserved names remain valid BoundaryKind-free: the policy
        // names are boundary kinds for external/stdlib positions, the
        // boundary names are never valid in version 1.
        check(enumMember(BoundaryKind.class, "EXTERNAL_PARAMETER")
                && enumMember(BoundaryKind.class, "EXTERNAL_RETURN")
                && enumMember(BoundaryKind.class, "STDLIB_PARAMETER")
                && enumMember(BoundaryKind.class, "STDLIB_RETURN"),
            "the four reserved policy names remain valid BoundaryKind values "
                + "(external/stdlib positions)");
    }

    // =========================================================================
    // 2. Positive corpus: one passing unit per row of the closed table (a)-(k)
    // =========================================================================

    /** (a) The descriptor-kind-rule cells for the core boundary kinds, both descriptor arms. */
    private static List<Row> rowsA() {
        List<Row> rows = new ArrayList<>();
        List<BoundaryKind> coreKinds = List.of(
            BoundaryKind.VARIABLE_DECLARATION, BoundaryKind.VARIABLE_ASSIGNMENT,
            BoundaryKind.CLASS_FIELD_ASSIGNMENT, BoundaryKind.UNTYPED_CLASS_INPUT,
            BoundaryKind.OPTIONAL_FIELD_READ, BoundaryKind.CONTEXTUAL_TABLE_READ,
            BoundaryKind.IMPORTED_MEMBER_READ, BoundaryKind.MODULE_EXPORT);
        for (BoundaryKind kind : coreKinds) {
            rows.add(single("a." + kind.name() + ".nonFunction", "a",
                unit(List.of(boundary(kind, STRING, FailurePolicyId.TYPE_DESCRIPTOR, null)))));
            rows.add(single("a." + kind.name() + ".function", "a",
                unit(List.of(boundary(kind, F_IS, FailurePolicyId.FUNCTION_SIGNATURE, null)))));
        }
        return rows;
    }

    /** (b) The pinned host-direction cells: CALL(HOST) parameters and sync return. */
    private static Row rowB() {
        OpId callOp = nextOpId();
        OpId pb1 = nextOpId();
        OpId pb2 = nextOpId();
        OpId rb = nextOpId();
        FunctionExecutionBinding.HostFunction binding =
            new FunctionExecutionBinding.HostFunction(MOD_HOST, "add", F_IIS);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(pb1, BoundaryKind.DEAL_TO_HOST, INT,
            FailurePolicyId.HOST_PARAMETER, callOp));
        ops.add(boundaryWith(pb2, BoundaryKind.DEAL_TO_HOST, INT,
            FailurePolicyId.HOST_PARAMETER, callOp));
        ops.add(boundaryWith(rb, BoundaryKind.HOST_TO_DEAL, STRING,
            FailurePolicyId.HOST_SYNC_RETURN, callOp));
        ops.add(opWith(callOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.HOST,
                new KindPayload.CallCallee.Static(binding),
                F_IIS, List.of(pb1, pb2), rb, null, null, null),
            nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
        return single("b.CALL_HOST", "b", unit(ops));
    }

    /** (c) CALL(INDIRECT) → AdapterBinding rows for every source kind. */
    private static List<Row> rowsC() {
        List<Row> rows = new ArrayList<>();

        // DEAL-body source: xN target-signature FUNCTION_PARAMETER +
        // FUNCTION_RETURN executed by the source RETURN.
        {
            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            OpId returnOp = nextOpId();
            long calleeId = 101;
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(1), 0), F_II, F_IIS);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), callOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("c.adapter.dealBody", "c",
                unit(Map.of(new FunctionAllocationIdentity(calleeId), binding), ops)));
        }

        // Host source: xN FUNCTION_PARAMETER + HOST_TO_DEAL + HOST_SYNC_RETURN by the call op.
        {
            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            long calleeId = 102;
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(2), 0), F_II, F_IIS);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.HOST_TO_DEAL, STRING,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("c.adapter.hostSource", "c",
                unit(Map.of(new FunctionAllocationIdentity(calleeId), binding), ops)));
        }

        // External RETAINED_ABI source: xN FUNCTION_PARAMETER + call-op EXTERNAL_RETURN.
        {
            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            long calleeId = 103;
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(3), 0), F_II, F_IIS);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("c.adapter.externalRetained", "c",
                unit(Map.of(new FunctionAllocationIdentity(calleeId), binding), ops)));
        }

        // External SHARED_BODY source: xN FUNCTION_PARAMETER caller-side +
        // callee-side EXTERNAL_RETURN under EXTERNAL_ENTRY (cross-unit project).
        {
            OpId entryOp = nextOpId(MOD_B);
            OpId rb = nextOpId(MOD_B);
            OpId returnOp = nextOpId(MOD_B);
            List<SemanticOp> calleeOps = new ArrayList<>();
            calleeOps.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            calleeOps.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), entryOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            calleeOps.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS, false, rb,
                    null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit callee = unit(MOD_B, Set.of(), Map.of(), calleeOps);

            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            long calleeId = 104;
            FunctionExecutionBinding.AdapterBinding binding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(4), 0), F_II, F_IIS);
            List<SemanticOp> callerOps = new ArrayList<>();
            callerOps.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            callerOps.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            callerOps.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit caller =
                unit(MOD, Set.of(), Map.of(new FunctionAllocationIdentity(calleeId), binding),
                    callerOps);
            rows.add(projectRow("c.adapter.externalShared", "c",
                List.of(caller, callee), MOD));
        }

        return rows;
    }

    /** (d) The CALLBACK_INVOKE rows (host-driven invocation of a DEAL function value). */
    private static List<Row> rowsD() {
        List<Row> rows = new ArrayList<>();
        rows.add(callbackRow("d.callback.loweredBody", 201,
            new FunctionExecutionBinding.LoweredBody(new FunctionId(2), new BlockId(2)), true));
        rows.add(callbackRow("d.callback.adapterDealBody", 202,
            new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(new BindingId(5), 0), F_II, F_IIS), true));
        rows.add(callbackRow("d.callback.adapterHostSource", 203,
            new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(new BindingId(6), 0), F_II, F_IIS), false));
        rows.add(callbackRow("d.callback.adapterExternalSource", 204,
            new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                new AdaptSourceRef.SharedCell(new BindingId(7), 0), F_II, F_IIS), false));
        rows.add(callbackRow("d.callback.hostFunction", 205,
            new FunctionExecutionBinding.HostFunction(MOD_HOST, "cb", F_IIS), false));
        rows.add(callbackHostFunctionValueRow());
        rows.add(callbackRow("d.callback.externalFunction", 207,
            new FunctionExecutionBinding.ExternalFunction(MOD_B, "cb", F_IIS,
                ExternalExecutionOwner.RETAINED_ABI), false));
        return rows;
    }

    /** One CALLBACK_INVOKE row: N HOST_TO_DEAL parameters + the single DEAL_TO_HOST return
     *  (by the executed body's RETURN when {@code bodyReturn} — the pinned owner per row). */
    private static Row callbackRow(String name, long allocationId,
                                   FunctionExecutionBinding binding, boolean bodyReturn) {
        OpId callbackOp = nextOpId();
        OpId pb1 = nextOpId();
        OpId pb2 = nextOpId();
        OpId rb = nextOpId();
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(pb1, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        ops.add(boundaryWith(pb2, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        if (bodyReturn) {
            OpId returnOp = nextOpId();
            ops.add(boundaryWith(rb, BoundaryKind.DEAL_TO_HOST, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(3), callbackOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        } else {
            ops.add(boundaryWith(rb, BoundaryKind.DEAL_TO_HOST, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        }
        ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
            new KindPayload.CallbackInvokePayload(new ValueId(allocationId), F_IIS,
                List.of(pb1, pb2), rb),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return single(name, "d",
            unit(Map.of(new FunctionAllocationIdentity(allocationId), binding), ops));
    }

    /**
     * The {@code d.callback.hostFunctionValue} row: the bound function's
     * {@code HostFunctionValue} registration carries its real correlation
     * id — the producing host crossing, a {@code CALL(HOST)} whose single
     * {@code HOST_TO_DEAL} + {@code HOST_SYNC_RETURN} sync-return boundary
     * materializes the function value (input identity 206, the call's
     * result identity) with the registration's checked descriptor.
     */
    private static Row callbackHostFunctionValueRow() {
        OpId callbackOp = nextOpId();
        OpId cbPb1 = nextOpId();
        OpId cbPb2 = nextOpId();
        OpId cbRb = nextOpId();
        OpId hostCallOp = nextOpId();
        OpId hostCallRb = nextOpId();
        RuntimeDescriptor.Func zeroToFunc = new RuntimeDescriptor.Func(List.of(), F_IIS);
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(cbPb1, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        ops.add(boundaryWith(cbPb2, BoundaryKind.HOST_TO_DEAL, INT,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        ops.add(boundaryWith(cbRb, BoundaryKind.DEAL_TO_HOST, STRING,
            FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
        ops.add(opWith(hostCallRb, SemanticOpKind.BOUNDARY,
            new KindPayload.BoundaryPayload(BoundaryKind.HOST_TO_DEAL, F_IIS,
                new ValueId(206), new BoundaryRealization.RuntimeValidation("check-206")),
            null, null, FailurePolicyId.HOST_SYNC_RETURN, hostCallOp));
        ops.add(opWith(hostCallOp, SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.HOST,
                new KindPayload.CallCallee.Static(new FunctionExecutionBinding.HostFunction(
                    MOD_HOST, "materialize", zeroToFunc)),
                zeroToFunc, List.of(), hostCallRb, null, null, null),
            new ValueId(206), F_IIS, FailurePolicyId.NO_DEAL_FAILURE, null));
        ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
            new KindPayload.CallbackInvokePayload(new ValueId(206), F_IIS,
                List.of(cbPb1, cbPb2), cbRb),
            null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
        return single("d.callback.hostFunctionValue", "d",
            unit(Map.of(new FunctionAllocationIdentity(206),
                    new FunctionExecutionBinding.HostFunctionValue(MOD_HOST, hostCallRb, F_IIS)),
                ops));
    }

    /** (e) The core array element cells, each under its pinned parent. */
    private static List<Row> rowsE() {
        List<Row> rows = new ArrayList<>();

        // ARRAY_LITERAL_ELEMENT → ARRAY_ELEMENT_DESCRIPTOR under ARRAY_NEW.
        {
            OpId arrayOp = nextOpId();
            OpId elementBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
                FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR, arrayOp));
            ops.add(opWith(arrayOp, SemanticOpKind.ARRAY_NEW,
                new KindPayload.ArrayNewPayload(INT, List.of(nextValue()),
                    List.of(elementBoundary)),
                nextValue(), ARRAY_INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("e.arrayLiteralElement", "e", unit(ops)));
        }

        // ARRAY_ELEMENT_READ → ARRAY_READ_INDEX_THEN_DESCRIPTOR under INDEX_READ.
        {
            OpId indexReadOp = nextOpId();
            OpId readBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(readBoundary, BoundaryKind.ARRAY_ELEMENT_READ, INT,
                FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, indexReadOp));
            ops.add(opWith(indexReadOp, SemanticOpKind.INDEX_READ,
                new KindPayload.IndexReadPayload(nextValue(), nextValue(), readBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            {
                BoundaryValueView intView = BoundaryValueView.ofInt(7);
                rows.add(single("e.arrayElementRead", "e", unit(ops), armsOf(readBoundary,
                    new ExecArm(intView, BoundaryContext.arrayIndex(-1),
                        new ExecFail(DiagnosticCode.E8002, "negative array index", null, null,
                            new LinkedHashMap<>())),
                    new ExecArm(intView, BoundaryContext.arrayIndex(0),
                        new ExecPass(intView, true)))));
            }
        }

        // ARRAY_ELEMENT_ASSIGNMENT → ARRAY_WRITE_BOUNDS_THEN_ELEMENT under ASSIGN ARRAY_SLOT.
        {
            OpId assignOp = nextOpId();
            OpId assignBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(assignBoundary, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, assignOp));
            ops.add(opWith(assignOp, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(deal.semantic.ir.AssignTargetKind.ARRAY_SLOT,
                    List.of(nextOpId(), nextOpId(), nextOpId(), assignBoundary, nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            {
                BoundaryValueView intView = BoundaryValueView.ofInt(7);
                rows.add(single("e.arrayElementAssignment", "e", unit(ops), armsOf(assignBoundary,
                    new ExecArm(intView, BoundaryContext.writeBounds(4, 3),
                        new ExecFail(DiagnosticCode.E8002, "array index out of bounds", null, null,
                            new LinkedHashMap<>())),
                    new ExecArm(intView, BoundaryContext.writeBounds(1, 3),
                        new ExecPass(intView, true)))));
            }
        }

        // ARRAY_ELEMENT_DELETE → ARRAY_DELETE_BOUNDS under DELETE ARRAY_SLOT.
        {
            OpId deleteOp = nextOpId();
            OpId deleteBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(deleteBoundary, BoundaryKind.ARRAY_ELEMENT_DELETE, INT,
                FailurePolicyId.ARRAY_DELETE_BOUNDS, deleteOp));
            ops.add(opWith(deleteOp, SemanticOpKind.DELETE,
                new KindPayload.DeletePayload(DeleteTargetKind.ARRAY_SLOT,
                    List.of(nextOpId(), nextOpId(), deleteBoundary, nextOpId())),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            {
                BoundaryValueView intView = BoundaryValueView.ofInt(7);
                rows.add(single("e.arrayElementDelete", "e", unit(ops), armsOf(deleteBoundary,
                    new ExecArm(intView, BoundaryContext.writeBounds(4, 3),
                        new ExecFail(DiagnosticCode.E8002, "array index out of bounds", null, null,
                            new LinkedHashMap<>())),
                    new ExecArm(intView, BoundaryContext.writeBounds(1, 3),
                        new ExecPass(intView, true)))));
            }
        }

        return rows;
    }

    /** (f) The external cells (SHARED_BODY, RETAINED_ABI) and the stdlib cells. */
    private static List<Row> rowsF() {
        List<Row> rows = new ArrayList<>();

        // CALL(EXTERNAL) SHARED_BODY: caller-side EXTERNAL_PARAMETER xN +
        // callee-side EXTERNAL_RETURN under EXTERNAL_ENTRY (cross-unit project).
        {
            OpId entryOp = nextOpId(MOD_B);
            OpId rb = nextOpId(MOD_B);
            OpId returnOp = nextOpId(MOD_B);
            List<SemanticOp> calleeOps = new ArrayList<>();
            calleeOps.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            calleeOps.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), entryOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            calleeOps.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS, false, rb,
                    null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit callee = unit(MOD_B, Set.of(), Map.of(), calleeOps);

            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            FunctionExecutionBinding.ExternalFunction binding =
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", F_IIS,
                    ExternalExecutionOwner.SHARED_BODY);
            List<SemanticOp> callerOps = new ArrayList<>();
            callerOps.add(boundaryWith(pb1, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            callerOps.add(boundaryWith(pb2, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            callerOps.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(binding),
                    F_IIS, List.of(pb1, pb2), null, null, null, entryOp),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit caller = unit(MOD, Set.of(),
                Map.of(new FunctionAllocationIdentity(301), binding), callerOps);
            rows.add(projectRow("f.externalSharedBody", "f", List.of(caller, callee), MOD));
        }

        // CALL(EXTERNAL) RETAINED_ABI: EXTERNAL_PARAMETER xN + call-op EXTERNAL_RETURN.
        {
            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            FunctionExecutionBinding.ExternalFunction binding =
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", F_IIS,
                    ExternalExecutionOwner.RETAINED_ABI);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(pb2, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(binding),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("f.externalRetainedAbi", "f",
                unit(Map.of(new FunctionAllocationIdentity(302), binding), ops)));
        }

        // STDLIB_CALL: STDLIB_PARAMETER + STDLIB_RETURN under the descriptor-kind rule.
        {
            OpId stdlibOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.STDLIB_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, stdlibOp));
            ops.add(boundaryWith(rb, BoundaryKind.STDLIB_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, stdlibOp));
            ops.add(opWith(stdlibOp, SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(StdlibFunctionId.MATH_ABS_INT,
                    List.of(nextValue()), SemanticCapability.STDLIB_SEMANTICS),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null));
            rows.add(single("f.stdlib", "f", unit(ops)));
        }

        return rows;
    }

    /** (g) The EXTERNAL_ENTRY row: sync (single EXTERNAL_RETURN) and async
     *  (single FUNCTION_RETURN). */
    private static List<Row> rowsG() {
        List<Row> rows = new ArrayList<>();

        {
            OpId entryOp = nextOpId();
            OpId rb = nextOpId();
            OpId returnOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), entryOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS, false, rb,
                    null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("g.entrySync", "g", unit(ops)));
        }

        {
            OpId entryOp = nextOpId();
            OpId rb = nextOpId();
            OpId returnOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            ops.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), entryOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS_ASYNC, true,
                    rb, STRING),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            rows.add(single("g.entryAsync", "g", unit(ops)));
        }

        return rows;
    }

    /** (h) The ASYNC_START rows, each with its single AWAIT + ASYNC_COMPLETION. */
    private static List<Row> rowsH() {
        List<Row> rows = new ArrayList<>();

        // DEAL_BODY: FUNCTION_PARAMETER params + body-task FUNCTION_RETURN + one ASYNC_COMPLETION.
        {
            OpId startOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            AsyncTokenId token = new AsyncTokenId.Canonical(1, AsyncTokenOwner.DEAL_BODY_TASK);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(pb1, pb2), INT, rb, null, null),
                token, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.addAll(awaitOps(token, INT));
            rows.add(single("h.asyncDealBody", "h", unit(ops)));
        }

        // Adapter-over-async (DEAL-body nested source): xN target-signature
        // FUNCTION_PARAMETER on the outer op, zero outer return boundaries,
        // the nested source op ELIDED_BY_ADAPTER with zero parameters and
        // its own FUNCTION_RETURN body-task terminal; the outer token is an
        // ADAPTER_INNER alias, never canonical.
        {
            OpId outerOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            FunctionExecutionBinding.AdapterBinding outerBinding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(8), 0), F_II, F_IIS);
            AsyncTokenId inner = new AsyncTokenId.Canonical(2, AsyncTokenOwner.DEAL_BODY_TASK);
            AsyncTokenId outer = new AsyncTokenId.Alias(3, inner, AsyncLinkKind.ADAPTER_INNER);
            OpId nestedOp = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, nestedOp));
            ops.add(opWith(outerOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(outerBinding),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(pb1, pb2), STRING, null, null, null),
                outer, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(nestedOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(2),
                            new BlockId(2))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.ELIDED_BY_ADAPTER,
                    List.of(), STRING, rb, null, null),
                inner, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE,
                outerOp));
            ops.addAll(awaitOps(outer, STRING));
            rows.add(single("h.adapterOverAsyncBody", "h", unit(ops)));
        }

        // Adapter-over-async (async HOST nested source): the nested source
        // op runs ELIDED_BY_ADAPTER with zero parameters and the HOST
        // per-resolution terminal (zero return boundaries).
        {
            OpId outerOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            FunctionExecutionBinding.AdapterBinding outerBinding =
                new FunctionExecutionBinding.AdapterBinding(nextOpId(), CaptureMode.SHARED_CELL,
                    new AdaptSourceRef.SharedCell(new BindingId(9), 0), F_II, F_IIS);
            AsyncTokenId inner = new AsyncTokenId.Canonical(4, AsyncTokenOwner.HOST_OPERATION);
            AsyncTokenId outer = new AsyncTokenId.Alias(5, inner, AsyncLinkKind.ADAPTER_INNER);
            OpId nestedOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(pb2, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(opWith(outerOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(outerBinding),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN,
                    List.of(pb1, pb2), STRING, null, null, null),
                outer, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(nestedOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.ELIDED_BY_ADAPTER,
                    List.of(), STRING, null, "op-1", null),
                inner, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE,
                outerOp));
            ops.addAll(awaitOps(outer, STRING));
            rows.add(single("h.adapterOverAsyncHost", "h", unit(ops)));
        }

        // ASYNC_START(HOST): DEAL_TO_HOST + HOST_PARAMETER params, zero
        // return boundaries, one ASYNC_COMPLETION at the single AWAIT.
        {
            OpId startOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            AsyncTokenId token = new AsyncTokenId.Canonical(6, AsyncTokenOwner.HOST_OPERATION);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, startOp));
            ops.add(boundaryWith(pb2, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.RUN,
                    List.of(pb1, pb2), STRING, null, "op-2", null),
                token, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.addAll(awaitOps(token, STRING));
            rows.add(single("h.asyncHost", "h", unit(ops)));
        }

        // ASYNC_START(EXTERNAL): caller-side EXTERNAL_PARAMETER xN, zero
        // caller return boundaries, callee-task FUNCTION_RETURN in the
        // callee unit, one caller ASYNC_COMPLETION (cross-unit project).
        {
            OpId entryOp = nextOpId(MOD_B);
            OpId rb = nextOpId(MOD_B);
            OpId returnOp = nextOpId(MOD_B);
            List<SemanticOp> calleeOps = new ArrayList<>();
            calleeOps.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, returnOp));
            calleeOps.add(opWith(returnOp, SemanticOpKind.RETURN,
                new KindPayload.ReturnPayload(nextValue(), new FunctionId(1), entryOp, rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            calleeOps.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS_ASYNC, true,
                    rb, STRING),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            LoweredModuleUnit callee = unit(MOD_B, Set.of(), Map.of(), calleeOps);

            OpId startOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            FunctionExecutionBinding.ExternalFunction binding =
                new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", F_IIS_ASYNC,
                    ExternalExecutionOwner.SHARED_BODY);
            AsyncTokenId calleeToken =
                new AsyncTokenId.Canonical(7, AsyncTokenOwner.DEAL_BODY_TASK);
            AsyncTokenId callerToken =
                new AsyncTokenId.Alias(8, calleeToken, AsyncLinkKind.EXTERNAL_LINK);
            ExternalAsyncLink link = new ExternalAsyncLink(MOD_B, "f", calleeToken);
            List<SemanticOp> callerOps = new ArrayList<>();
            callerOps.add(boundaryWith(pb1, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            callerOps.add(boundaryWith(pb2, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            callerOps.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(binding),
                    AsyncStartSource.EXTERNAL, ParameterBoundaryMode.RUN,
                    List.of(pb1, pb2), STRING, null, null, link),
                callerToken, InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE,
                null));
            callerOps.addAll(awaitOps(callerToken, STRING));
            LoweredModuleUnit caller = unit(MOD, Set.of(),
                Map.of(new FunctionAllocationIdentity(401), binding), callerOps);
            rows.add(projectRow("h.asyncExternal", "h", List.of(caller, callee), MOD));
        }

        return rows;
    }

    /** The AWAIT + ASYNC_COMPLETION tail ops shared by the async rows. */
    private static List<SemanticOp> awaitOps(AsyncTokenId token, RuntimeDescriptor completion) {
        OpId awaitOp = nextOpId();
        OpId completionBoundary = nextOpId();
        List<SemanticOp> ops = new ArrayList<>();
        ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, completion,
            FailurePolicyId.ASYNC_COMPLETION, awaitOp));
        ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
            new KindPayload.AwaitPayload(token, completion, completionBoundary),
            nextValue(), completion, FailurePolicyId.NO_DEAL_FAILURE, null));
        return ops;
    }

    /** (i) The AWAIT completion cell: kind ASYNC_COMPLETION + policy ASYNC_COMPLETION. */
    private static Row rowI() {
        AsyncTokenId token = new AsyncTokenId.Canonical(9, AsyncTokenOwner.DEAL_BODY_TASK);
        return single("i.awaitCompletion", "i", unit(awaitOps(token, INT)));
    }

    /** (j) The zero-boundary shapes. */
    private static List<Row> rowsJ() {
        List<Row> rows = new ArrayList<>();

        // INTRINSIC_CALL: zero BOUNDARY children of any kind.
        rows.add(single("j.intrinsicZeroBoundaries", "j", unit(List.of(
            op(SemanticOpKind.INTRINSIC_CALL,
                new KindPayload.IntrinsicCallPayload(IntrinsicKind.INT_CONVERT, nextValue()),
                nextValue(), INT, FailurePolicyId.INT_CONVERSION, null)))));

        // CLASS_NEW: only CLASS_LITERAL_FIELD / CLASS_DEFAULT_FIELD field
        // boundaries under the descriptor-kind rule; zero return boundaries.
        {
            ClassId classId = new ClassId("mod.a", "C");
            ClassLayout layout = new ClassLayout(classId,
                List.of(new ClassLayout.FieldLayout("f", INT, true, DefaultOwner.LOCAL)));
            OpId classNewOp = nextOpId();
            OpId literalBoundary = nextOpId();
            OpId defaultBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(literalBoundary, BoundaryKind.CLASS_LITERAL_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(boundaryWith(defaultBoundary, BoundaryKind.CLASS_DEFAULT_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(opWith(classNewOp, SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(classId, layout,
                    List.of(new KindPayload.ProvidedField("f", nextValue())),
                    DefaultOwner.LOCAL, List.of(), null,
                    List.of(new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_LITERAL_FIELD,
                            literalBoundary),
                        new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_DEFAULT_FIELD,
                            defaultBoundary))),
                nextValue(), new RuntimeDescriptor.Class(classId),
                FailurePolicyId.CLASS_CONSTRUCTION, null));
            rows.add(single("j.classNewFieldBoundaries", "j", unit(ops)));
        }

        // CLASS_FACTORY: zero boundary children.
        rows.add(single("j.classFactoryZeroBoundaries", "j", unit(List.of(
            op(SemanticOpKind.CLASS_FACTORY,
                new KindPayload.ClassFactoryPayload(new ClassId("mod.a", "C"), List.of(),
                    nextOpId()),
                null, null, FailurePolicyId.CLASS_CONSTRUCTION, null)))));

        return rows;
    }

    /** (k) The JSON exception cells, executed through the executor's pinned arms. */
    private static List<Row> rowsK() {
        List<Row> rows = new ArrayList<>();

        // JSON_FROM_FIELD + JSON_FROM_NULL: the swallow maps any failure to
        // language null and never raises a DEAL failure.
        {
            OpId jsonFrom = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(jsonFrom, BoundaryKind.JSON_FROM_FIELD, STRING,
                FailurePolicyId.JSON_FROM_NULL, null));
            {
                BoundaryValueView stringView = BoundaryValueView.of(ActualKind.STRING);
                rows.add(single("k.jsonFromField", "k", unit(ops), armsOf(jsonFrom,
                    new ExecArm(BoundaryValueView.ofNumber(1.5), BoundaryContext.none(),
                        new ExecPass(BoundaryValueView.nullView(), false)),
                    new ExecArm(stringView, BoundaryContext.none(),
                        new ExecPass(stringView, true)))));
            }
        }

        // JSON_TO_FIELD + JSON_TO_ERROR: the first unsupported value
        // projects E8001 `value at {fieldPath} is not JSON serializable:
        // {actual}` with the context fieldPath.
        {
            OpId jsonTo = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(jsonTo, BoundaryKind.JSON_TO_FIELD, INT,
                FailurePolicyId.JSON_TO_ERROR, null));
            Map<String, String> metadata = new LinkedHashMap<>();
            metadata.put("fieldPath", "f");
            {
                BoundaryValueView intView = BoundaryValueView.ofInt(7);
                rows.add(single("k.jsonToField", "k", unit(ops), armsOf(jsonTo,
                    new ExecArm(BoundaryValueView.ofNumber(Double.NaN),
                        BoundaryContext.jsonField("f"),
                        new ExecFail(DiagnosticCode.E8001,
                            "value at f is not JSON serializable: number", null, "number",
                            metadata)),
                    new ExecArm(intView, BoundaryContext.jsonField("f"),
                        new ExecPass(intView, true)))));
            }
        }

        return rows;
    }

    /** The complete enumerated positive row list (a)-(k), 48 rows in total. */
    private static List<Row> positiveRows() {
        List<Row> rows = new ArrayList<>();
        rows.addAll(rowsA());
        rows.add(rowB());
        rows.addAll(rowsC());
        rows.addAll(rowsD());
        rows.addAll(rowsE());
        rows.addAll(rowsF());
        rows.addAll(rowsG());
        rows.addAll(rowsH());
        rows.add(rowI());
        rows.addAll(rowsJ());
        rows.addAll(rowsK());
        return rows;
    }

    // =========================================================================
    // Positive-corpus runner: validation, payload inspection, executor tie, sweeps
    // =========================================================================

    private static Optional<CompilerDiagnostic> validateRow(Row row) {
        if (row.units().size() == 1) {
            return SemanticIrValidator.validate(row.units().get(0), FACTS);
        }
        return SemanticIrValidator.validate(projectOf(row.units(), row.entry()), FACTS);
    }

    private static Optional<CompilerDiagnostic> validateRowText(Row row) {
        if (row.units().size() == 1) {
            return SemanticIrValidator.validateText(
                SemanticIrValidator.toUnitText(row.units().get(0)), FACTS);
        }
        return SemanticIrValidator.validateText(
            SemanticIrValidator.toProjectText(projectOf(row.units(), row.entry())), FACTS);
    }

    private static void runExecutorTie(Row row) {
        for (LoweredModuleUnit unit : row.units()) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.BOUNDARY) {
                    continue;
                }
                KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
                List<ExecArm> arms = row.arms().get(op.opId());
                if (arms == null) {
                    BoundaryValueView view = matchingView(payload.descriptor());
                    BoundaryOutcome outcome = BoundaryExecutor.check(op.failurePolicy(),
                        payload.descriptor(), view, defaultContext(op.failurePolicy()));
                    assertExec(outcome, new ExecPass(view, true),
                        row.name() + " default tie arm on " + op.opId() + " (" + payload.kind()
                            + ", " + op.failurePolicy() + ")");
                } else {
                    for (ExecArm arm : arms) {
                        BoundaryOutcome outcome = BoundaryExecutor.check(op.failurePolicy(),
                            payload.descriptor(), arm.view(), arm.context());
                        assertExec(outcome, arm.expected(),
                            row.name() + " tie arm on " + op.opId() + " (" + payload.kind()
                                + ", " + op.failurePolicy() + ")");
                    }
                }
            }
        }
    }

    private static long countBoundaries(List<LoweredModuleUnit> units, BoundaryKind kind) {
        long count = 0;
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) op.payload()).kind() == kind) {
                    count++;
                }
            }
        }
        return count;
    }

    private static long countBoundaries(List<LoweredModuleUnit> units, BoundaryKind kind,
                                        FailurePolicyId policy) {
        long count = 0;
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) op.payload()).kind() == kind
                        && op.failurePolicy() == policy) {
                    count++;
                }
            }
        }
        return count;
    }

    private static Row rowByName(List<Row> rows, String name) {
        for (Row row : rows) {
            if (row.name().equals(name)) {
                return row;
            }
        }
        return null;
    }

    private static SemanticOp opById(List<LoweredModuleUnit> units, OpId opId) {
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.opId().equals(opId)) {
                    return op;
                }
            }
        }
        return null;
    }

    private static KindPayload.BoundaryPayload boundaryPayload(SemanticOp op) {
        return (KindPayload.BoundaryPayload) op.payload();
    }

    static void testPositiveCorpus(List<Row> rows) {
        System.out.println("-- Positive corpus: one passing unit per row of the closed table --");

        // Row enumeration: exactly the (a)-(k) families, every row name unique.
        check(rows.size() == 48,
            "the corpus enumerates exactly 48 positive rows (a)-(k); got " + rows.size());
        Set<String> families = new LinkedHashSet<>();
        Set<String> names = new LinkedHashSet<>();
        for (Row row : rows) {
            families.add(row.family());
            check(names.add(row.name()), "row name is unique: " + row.name());
        }
        check(families.equals(new LinkedHashSet<>(List.of("a", "b", "c", "d", "e", "f", "g",
                "h", "i", "j", "k"))),
            "every row family (a)-(k) has at least one unit; got " + families);

        // Every row validates on the typed surface (unit or cross-unit
        // project) and on the canonical-JSON text surface.
        for (Row row : rows) {
            assertPass(validateRow(row), "positive row " + row.name());
            assertPass(validateRowText(row), "positive row " + row.name() + " through the text surface");
        }

        // The validator/executor tie: every BOUNDARY op of every positive
        // row executes through BoundaryExecutor.check with its pinned
        // Pass/failure projection.
        for (Row row : rows) {
            runExecutorTie(row);
        }

        // Every validated boundary carries its active realization directly
        // in the Semantic IR payload.
        for (Row row : rows) {
            for (LoweredModuleUnit unit : row.units()) {
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.BOUNDARY) {
                        BoundaryRealization realization = boundaryPayload(op).realization();
                        check(realization instanceof BoundaryRealization.RuntimeValidation,
                            row.name() + " boundary " + op.opId()
                                + " carries a RuntimeValidation realization");
                        if (realization instanceof BoundaryRealization.RuntimeValidation validation) {
                            check(!validation.checkId().isEmpty(),
                                row.name() + " boundary " + op.opId()
                                    + " carries a non-empty runtime validation id");
                        }
                    }
                }
            }
        }

        // The closed-kind sweep: all 25 BoundaryKind values appear in the
        // positive corpus, and the closed 11-policy executor subset appears
        // exactly as a BOUNDARY op policy.
        Set<BoundaryKind> kinds = new LinkedHashSet<>();
        Set<FailurePolicyId> policies = new LinkedHashSet<>();
        for (Row row : rows) {
            for (LoweredModuleUnit unit : row.units()) {
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.BOUNDARY) {
                        kinds.add(boundaryPayload(op).kind());
                        policies.add(op.failurePolicy());
                    }
                }
            }
        }
        // ISSUE-0626 retargeted this pin: the two bytes element cells carry
        // their own {index, length} contexts and their own parent shapes (the
        // INDEX_READ read shape and the seven-child BYTES_SLOT chain), so
        // their positive rows are the bytes slice's own vertical drive
        // (test/BytesCoverageTest) — every other kind stays covered here.
        List<BoundaryKind> corpusKinds = List.of(BoundaryKind.values()).stream()
            .filter(kind -> kind != BoundaryKind.BYTE_ELEMENT_READ
                && kind != BoundaryKind.BYTE_ELEMENT_ASSIGNMENT)
            .toList();
        check(kinds.equals(new LinkedHashSet<>(corpusKinds)),
            "every BoundaryKind value except the bytes element cells appears in the "
                + "positive corpus (the bytes cells' positive rows are the bytes "
                + "slice's own vertical drive); missing: "
                + corpusKinds.stream().filter(k -> !kinds.contains(k)).toList()
                + ", extra: "
                + kinds.stream().filter(k -> !corpusKinds.contains(k)).toList());
        check(policies.equals(new LinkedHashSet<>(List.of(
                FailurePolicyId.TYPE_DESCRIPTOR, FailurePolicyId.FUNCTION_SIGNATURE,
                FailurePolicyId.HOST_PARAMETER, FailurePolicyId.HOST_SYNC_RETURN,
                FailurePolicyId.ASYNC_COMPLETION, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
                FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT,
                FailurePolicyId.ARRAY_DELETE_BOUNDS, FailurePolicyId.JSON_FROM_NULL,
                FailurePolicyId.JSON_TO_ERROR))),
            "the BOUNDARY-op policy set of this positive corpus is exactly the 11 "
                + "non-bytes executor cells (the bytes element cells carry their own "
                + "{index, length} contexts and are covered by the bytes slice's own "
                + "vertical drive); got " + policies);
    }

    // =========================================================================
    // Per-mode boundary counts pinned in the corpus (conformance Verification 5)
    // =========================================================================

    static void testPerModeBoundaryCounts(List<Row> rows) {
        System.out.println("-- Per-mode boundary counts pinned in the corpus --");

        // (a) Descriptor-kind cells: exactly one boundary per arm.
        for (BoundaryKind kind : List.of(BoundaryKind.VARIABLE_DECLARATION,
                BoundaryKind.VARIABLE_ASSIGNMENT, BoundaryKind.CLASS_FIELD_ASSIGNMENT,
                BoundaryKind.UNTYPED_CLASS_INPUT, BoundaryKind.OPTIONAL_FIELD_READ,
                BoundaryKind.CONTEXTUAL_TABLE_READ, BoundaryKind.IMPORTED_MEMBER_READ,
                BoundaryKind.MODULE_EXPORT)) {
            Row nonFunction = rowByName(rows, "a." + kind.name() + ".nonFunction");
            Row function = rowByName(rows, "a." + kind.name() + ".function");
            check(nonFunction != null && function != null,
                "both descriptor arms exist for kind " + kind.name());
            if (nonFunction != null && function != null) {
                check(countBoundaries(nonFunction.units(), kind) == 1
                        && countBoundaries(nonFunction.units(), kind,
                            FailurePolicyId.TYPE_DESCRIPTOR) == 1,
                    kind.name() + " non-function arm is exactly one TYPE_DESCRIPTOR boundary");
                check(countBoundaries(function.units(), kind) == 1
                        && countBoundaries(function.units(), kind,
                            FailurePolicyId.FUNCTION_SIGNATURE) == 1,
                    kind.name() + " function arm is exactly one FUNCTION_SIGNATURE boundary");
            }
        }

        // Sync one-return-boundary counts.
        Row host = rowByName(rows, "b.CALL_HOST");
        check(countBoundaries(host.units(), BoundaryKind.DEAL_TO_HOST,
                FailurePolicyId.HOST_PARAMETER) == 2
                && countBoundaries(host.units(), BoundaryKind.HOST_TO_DEAL,
                    FailurePolicyId.HOST_SYNC_RETURN) == 1,
            "CALL(HOST): N=2 DEAL_TO_HOST+HOST_PARAMETER parameters, one HOST_TO_DEAL+"
                + "HOST_SYNC_RETURN return");

        Row adapterBody = rowByName(rows, "c.adapter.dealBody");
        check(countBoundaries(adapterBody.units(), BoundaryKind.FUNCTION_PARAMETER) == 2
                && countBoundaries(adapterBody.units(), BoundaryKind.FUNCTION_RETURN,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1,
            "adapter CALL (DEAL-body source): N=2 FUNCTION_PARAMETER + one FUNCTION_RETURN "
                + "(by the source RETURN)");
        // The pinned owner: the FUNCTION_RETURN boundary is executed by the
        // source RETURN, whose enclosingInvocationOpId names the CALL.
        {
            SemanticOp adapterCallOp = findOpOfKind(adapterBody.units(), SemanticOpKind.CALL);
            SemanticOp adapterReturnOp = boundaryParentOp(adapterBody.units(),
                BoundaryKind.FUNCTION_RETURN);
            SemanticOp adapterReturnBoundary = findBoundaryOp(adapterBody.units(),
                BoundaryKind.FUNCTION_RETURN);
            check(adapterCallOp != null && adapterReturnOp != null
                    && adapterReturnOp.kind() == SemanticOpKind.RETURN
                    && ((KindPayload.ReturnPayload) adapterReturnOp.payload())
                        .enclosingInvocationOpId().equals(adapterCallOp.opId())
                    && adapterReturnBoundary != null
                    && ((KindPayload.ReturnPayload) adapterReturnOp.payload())
                        .returnBoundaryOpId().equals(adapterReturnBoundary.opId()),
                "the adapter DEAL-body-source FUNCTION_RETURN is executed by the source "
                    + "RETURN naming the CALL as its enclosing invocation and the boundary "
                    + "as its return boundary");
        }

        Row adapterHost = rowByName(rows, "c.adapter.hostSource");
        check(countBoundaries(adapterHost.units(), BoundaryKind.FUNCTION_PARAMETER) == 2
                && countBoundaries(adapterHost.units(), BoundaryKind.HOST_TO_DEAL,
                    FailurePolicyId.HOST_SYNC_RETURN) == 1,
            "adapter CALL (host source): N=2 FUNCTION_PARAMETER + one HOST_TO_DEAL+"
                + "HOST_SYNC_RETURN by the call op");

        Row adapterExternalRetained = rowByName(rows, "c.adapter.externalRetained");
        check(countBoundaries(adapterExternalRetained.units(), BoundaryKind.FUNCTION_PARAMETER)
                == 2
                && countBoundaries(adapterExternalRetained.units(), BoundaryKind.EXTERNAL_RETURN)
                    == 1,
            "adapter CALL (external RETAINED_ABI source): N=2 FUNCTION_PARAMETER + one call-op "
                + "EXTERNAL_RETURN");

        Row adapterExternalShared = rowByName(rows, "c.adapter.externalShared");
        check(countBoundaries(adapterExternalShared.units(), BoundaryKind.FUNCTION_PARAMETER)
                == 2
                && countBoundaries(adapterExternalShared.units(), BoundaryKind.EXTERNAL_RETURN)
                    == 1,
            "adapter CALL (external SHARED_BODY source): N=2 FUNCTION_PARAMETER + one "
                + "callee-side EXTERNAL_RETURN under EXTERNAL_ENTRY");

        // CALLBACK rows: N HOST_TO_DEAL + one DEAL_TO_HOST with the pinned owner.
        for (String name : List.of("d.callback.loweredBody", "d.callback.adapterDealBody",
                "d.callback.adapterHostSource", "d.callback.adapterExternalSource",
                "d.callback.hostFunction", "d.callback.hostFunctionValue",
                "d.callback.externalFunction")) {
            Row callback = rowByName(rows, name);
            check(callback != null, "callback row exists: " + name);
            if (callback != null) {
                check(countBoundaries(callback.units(), BoundaryKind.HOST_TO_DEAL,
                        FailurePolicyId.TYPE_DESCRIPTOR) == 2
                        && countBoundaries(callback.units(), BoundaryKind.DEAL_TO_HOST,
                            FailurePolicyId.TYPE_DESCRIPTOR) == 1,
                    name + ": N=2 HOST_TO_DEAL parameters + one DEAL_TO_HOST return");
            }
        }
        // The pinned callback return owners: the executed body's RETURN for
        // body/DEAL-body-source-adapter rows, the callback op for the
        // host/external-source adapter and direct resolution rows.
        for (String name : List.of("d.callback.loweredBody", "d.callback.adapterDealBody")) {
            Row callback = rowByName(rows, name);
            SemanticOp callbackOp = findOpOfKind(callback.units(),
                SemanticOpKind.CALLBACK_INVOKE);
            SemanticOp returnParent = boundaryParentOp(callback.units(),
                BoundaryKind.DEAL_TO_HOST);
            check(callbackOp != null && returnParent != null
                    && returnParent.kind() == SemanticOpKind.RETURN
                    && ((KindPayload.ReturnPayload) returnParent.payload())
                        .enclosingInvocationOpId().equals(callbackOp.opId()),
                name + ": the single DEAL_TO_HOST is executed by the body's RETURN");
        }
        for (String name : List.of("d.callback.adapterHostSource",
                "d.callback.adapterExternalSource", "d.callback.hostFunction",
                "d.callback.hostFunctionValue", "d.callback.externalFunction")) {
            Row callback = rowByName(rows, name);
            SemanticOp callbackOp = findOpOfKind(callback.units(),
                SemanticOpKind.CALLBACK_INVOKE);
            SemanticOp returnParent = boundaryParentOp(callback.units(),
                BoundaryKind.DEAL_TO_HOST);
            check(callbackOp != null && returnParent != null
                    && returnParent.opId().equals(callbackOp.opId()),
                name + ": the single DEAL_TO_HOST is executed by the callback op");
        }

        // Array cells: exactly one boundary each with its pinned policy.
        check(countBoundaries(rowByName(rows, "e.arrayLiteralElement").units(),
                BoundaryKind.ARRAY_LITERAL_ELEMENT, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR)
                == 1,
            "ARRAY_NEW: exactly one ARRAY_LITERAL_ELEMENT+ARRAY_ELEMENT_DESCRIPTOR boundary");
        check(countBoundaries(rowByName(rows, "e.arrayElementRead").units(),
                BoundaryKind.ARRAY_ELEMENT_READ, FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR)
                == 1,
            "INDEX_READ: exactly one ARRAY_ELEMENT_READ+ARRAY_READ_INDEX_THEN_DESCRIPTOR boundary");
        check(countBoundaries(rowByName(rows, "e.arrayElementAssignment").units(),
                BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT) == 1,
            "ASSIGN ARRAY_SLOT: exactly one ARRAY_ELEMENT_ASSIGNMENT+"
                + "ARRAY_WRITE_BOUNDS_THEN_ELEMENT boundary");
        check(countBoundaries(rowByName(rows, "e.arrayElementDelete").units(),
                BoundaryKind.ARRAY_ELEMENT_DELETE, FailurePolicyId.ARRAY_DELETE_BOUNDS) == 1,
            "DELETE ARRAY_SLOT: exactly one ARRAY_ELEMENT_DELETE+ARRAY_DELETE_BOUNDS boundary");

        // External cells.
        Row externalShared = rowByName(rows, "f.externalSharedBody");
        check(countBoundaries(externalShared.units(), BoundaryKind.EXTERNAL_PARAMETER) == 2
                && countBoundaries(externalShared.units(), BoundaryKind.EXTERNAL_RETURN) == 1,
            "CALL(EXTERNAL) SHARED_BODY: N=2 caller-side EXTERNAL_PARAMETER + one callee-side "
                + "EXTERNAL_RETURN");
        Row externalRetained = rowByName(rows, "f.externalRetainedAbi");
        check(countBoundaries(externalRetained.units(), BoundaryKind.EXTERNAL_PARAMETER) == 2
                && countBoundaries(externalRetained.units(), BoundaryKind.EXTERNAL_RETURN) == 1,
            "CALL(EXTERNAL) RETAINED_ABI: N=2 EXTERNAL_PARAMETER + one call-op EXTERNAL_RETURN");
        Row stdlib = rowByName(rows, "f.stdlib");
        check(countBoundaries(stdlib.units(), BoundaryKind.STDLIB_PARAMETER,
                FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(stdlib.units(), BoundaryKind.STDLIB_RETURN,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1,
            "STDLIB_CALL: one STDLIB_PARAMETER + one STDLIB_RETURN under the descriptor-kind rule");

        // EXTERNAL_ENTRY rows.
        check(countBoundaries(rowByName(rows, "g.entrySync").units(),
                BoundaryKind.EXTERNAL_RETURN, FailurePolicyId.TYPE_DESCRIPTOR) == 1,
            "sync EXTERNAL_ENTRY: exactly one EXTERNAL_RETURN");
        check(countBoundaries(rowByName(rows, "g.entryAsync").units(),
                BoundaryKind.FUNCTION_RETURN, FailurePolicyId.TYPE_DESCRIPTOR) == 1,
            "async EXTERNAL_ENTRY: exactly one FUNCTION_RETURN");

        // Async counts.
        Row asyncDealBody = rowByName(rows, "h.asyncDealBody");
        check(countBoundaries(asyncDealBody.units(), BoundaryKind.FUNCTION_PARAMETER,
                FailurePolicyId.TYPE_DESCRIPTOR) == 2
                && countBoundaries(asyncDealBody.units(), BoundaryKind.FUNCTION_RETURN,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(asyncDealBody.units(), BoundaryKind.ASYNC_COMPLETION,
                    FailurePolicyId.ASYNC_COMPLETION) == 1,
            "ASYNC_START(DEAL_BODY): N=2 FUNCTION_PARAMETER + one body-task FUNCTION_RETURN + "
                + "one ASYNC_COMPLETION at the single AWAIT");

        Row adapterOverAsyncBody = rowByName(rows, "h.adapterOverAsyncBody");
        check(countBoundaries(adapterOverAsyncBody.units(), BoundaryKind.FUNCTION_PARAMETER,
                FailurePolicyId.TYPE_DESCRIPTOR) == 2
                && countBoundaries(adapterOverAsyncBody.units(), BoundaryKind.FUNCTION_RETURN,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(adapterOverAsyncBody.units(), BoundaryKind.ASYNC_COMPLETION,
                    FailurePolicyId.ASYNC_COMPLETION) == 1,
            "adapter-over-async (DEAL-body source): outer N=2 FUNCTION_PARAMETER, zero outer "
                + "return boundaries, the nested source's one FUNCTION_RETURN, one "
                + "ASYNC_COMPLETION");

        Row adapterOverAsyncHost = rowByName(rows, "h.adapterOverAsyncHost");
        check(countBoundaries(adapterOverAsyncHost.units(), BoundaryKind.FUNCTION_PARAMETER,
                FailurePolicyId.TYPE_DESCRIPTOR) == 2
                && countBoundaries(adapterOverAsyncHost.units(), BoundaryKind.FUNCTION_RETURN)
                    == 0
                && countBoundaries(adapterOverAsyncHost.units(), BoundaryKind.HOST_TO_DEAL) == 0
                && countBoundaries(adapterOverAsyncHost.units(), BoundaryKind.ASYNC_COMPLETION,
                    FailurePolicyId.ASYNC_COMPLETION) == 1,
            "adapter-over-async (HOST source): outer N=2 FUNCTION_PARAMETER, the nested HOST "
                + "source runs zero parameter/return boundaries, one ASYNC_COMPLETION");

        Row asyncHost = rowByName(rows, "h.asyncHost");
        check(countBoundaries(asyncHost.units(), BoundaryKind.DEAL_TO_HOST,
                FailurePolicyId.HOST_PARAMETER) == 2
                && countBoundaries(asyncHost.units(), BoundaryKind.FUNCTION_RETURN) == 0
                && countBoundaries(asyncHost.units(), BoundaryKind.HOST_TO_DEAL) == 0
                && countBoundaries(asyncHost.units(), BoundaryKind.ASYNC_COMPLETION,
                    FailurePolicyId.ASYNC_COMPLETION) == 1,
            "ASYNC_START(HOST): N=2 DEAL_TO_HOST+HOST_PARAMETER, zero return boundaries, one "
                + "ASYNC_COMPLETION");

        Row asyncExternal = rowByName(rows, "h.asyncExternal");
        check(countBoundaries(asyncExternal.units(), BoundaryKind.EXTERNAL_PARAMETER,
                FailurePolicyId.TYPE_DESCRIPTOR) == 2
                && countBoundaries(asyncExternal.units(), BoundaryKind.FUNCTION_RETURN,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(asyncExternal.units(), BoundaryKind.ASYNC_COMPLETION,
                    FailurePolicyId.ASYNC_COMPLETION) == 1,
            "ASYNC_START(EXTERNAL): N=2 caller-side EXTERNAL_PARAMETER, zero caller return "
                + "boundaries, one callee-task FUNCTION_RETURN, one caller ASYNC_COMPLETION");

        // Zero-boundary shapes.
        check(rowByName(rows, "j.intrinsicZeroBoundaries").units().get(0).ops().stream()
                .noneMatch(op -> op.kind() == SemanticOpKind.BOUNDARY),
            "INTRINSIC_CALL: zero BOUNDARY children of any kind");
        Row classNew = rowByName(rows, "j.classNewFieldBoundaries");
        check(countBoundaries(classNew.units(), BoundaryKind.CLASS_LITERAL_FIELD,
                FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(classNew.units(), BoundaryKind.CLASS_DEFAULT_FIELD,
                    FailurePolicyId.TYPE_DESCRIPTOR) == 1
                && countBoundaries(classNew.units(), BoundaryKind.FUNCTION_RETURN) == 0
                && countBoundaries(classNew.units(), BoundaryKind.EXTERNAL_RETURN) == 0
                && countBoundaries(classNew.units(), BoundaryKind.DEAL_TO_HOST) == 0,
            "CLASS_NEW: only the two field boundaries, zero return boundaries");
        check(rowByName(rows, "j.classFactoryZeroBoundaries").units().get(0).ops().stream()
                .noneMatch(op -> op.kind() == SemanticOpKind.BOUNDARY),
            "CLASS_FACTORY: zero boundary children");

        // The AWAIT completion cell.
        check(countBoundaries(rowByName(rows, "i.awaitCompletion").units(),
                BoundaryKind.ASYNC_COMPLETION, FailurePolicyId.ASYNC_COMPLETION) == 1,
            "AWAIT: exactly one ASYNC_COMPLETION+ASYNC_COMPLETION boundary at the single "
                + "completionBoundaryOpId");
    }

    /** The first op of a kind across the row's units (or null). */
    private static SemanticOp findOpOfKind(List<LoweredModuleUnit> units, SemanticOpKind kind) {
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == kind) {
                    return op;
                }
            }
        }
        return null;
    }

    /** The first boundary op of a kind across the row's units (or null). */
    private static SemanticOp findBoundaryOp(List<LoweredModuleUnit> units, BoundaryKind kind) {
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && boundaryPayload(op).kind() == kind) {
                    return op;
                }
            }
        }
        return null;
    }

    /** The parent op of the first boundary of a kind across the row's units (or null). */
    private static SemanticOp boundaryParentOp(List<LoweredModuleUnit> units, BoundaryKind kind) {
        for (LoweredModuleUnit unit : units) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && boundaryPayload(op).kind() == kind
                        && op.origin().parentOpId() != null) {
                    return opById(units, op.origin().parentOpId());
                }
            }
        }
        return null;
    }

    // =========================================================================
    // 3. Negative corpus: one out-of-table negative per row family
    // =========================================================================

    private static final Set<String> negativeRules = new LinkedHashSet<>();

    private static void negative(String name, String family,
                                 Optional<CompilerDiagnostic> diagnostic, String rule,
                                 String... contains) {
        assertE6005(diagnostic, rule, contains);
        negativeRules.add(rule);
        check(diagnostic.isPresent(), "negative " + name + " produces exactly one E6005");
    }

    static void testNegativeCorpus() {
        System.out.println("-- Negative corpus: one out-of-table triple per row family --");

        // (a) Wrong policy for the kind — the descriptor-kind rule's two arms.
        negative("a.nonFunction.wrongPolicy", "a", SemanticIrValidator.validate(
                unit(List.of(boundary(BoundaryKind.VARIABLE_DECLARATION, STRING,
                    FailurePolicyId.FUNCTION_SIGNATURE, null))), FACTS),
            SemanticIrValidator.R_BOUNDARY_TRIPLE, "VARIABLE_DECLARATION",
            "FUNCTION_SIGNATURE", "descriptor-kind rule");
        negative("a.function.wrongPolicy", "a", SemanticIrValidator.validate(
                unit(List.of(boundary(BoundaryKind.MODULE_EXPORT, F_IS,
                    FailurePolicyId.TYPE_DESCRIPTOR, null))), FACTS),
            SemanticIrValidator.R_BOUNDARY_TRIPLE, "MODULE_EXPORT", "TYPE_DESCRIPTOR",
            "descriptor-kind rule");

        // (b) Host-direction cells: wrong policy on the parameter cell and
        //     wrong kind on the host return cell.
        {
            OpId callOp = nextOpId();
            OpId pb1 = nextOpId();
            OpId pb2 = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb1, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, callOp));
            ops.add(boundaryWith(pb2, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.HOST_TO_DEAL, STRING,
                FailurePolicyId.HOST_SYNC_RETURN, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.HOST,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "add", F_IIS)),
                    F_IIS, List.of(pb1, pb2), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("b.hostParameter.wrongPolicy", "b",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "DEAL_TO_HOST", "HOST_PARAMETER");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.HOST_TO_DEAL, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.HOST,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "f", F_IS)),
                    F_IS, List.of(pb), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("b.hostReturn.wrongPolicy", "b",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "HOST_TO_DEAL", "HOST_SYNC_RETURN");
        }

        // (c) Adapter rows: wrong kind for the invocation shape.
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            long calleeId = 108;
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("c.adapterParameter.wrongKind", "c",
                SemanticIrValidator.validate(unit(Map.of(
                        new FunctionAllocationIdentity(calleeId),
                        new FunctionExecutionBinding.AdapterBinding(nextOpId(),
                            CaptureMode.SHARED_CELL,
                            new AdaptSourceRef.SharedCell(new BindingId(10), 0), F_II, F_IIS)),
                    ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "FUNCTION_PARAMETER");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            long calleeId = 109;
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.DEAL_TO_HOST, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.INDIRECT,
                    new KindPayload.CallCallee.Indirect(new ValueId(calleeId)),
                    F_IIS, List.of(pb), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("c.adapterReturn.outOfTableKind", "c",
                SemanticIrValidator.validate(unit(Map.of(
                        new FunctionAllocationIdentity(calleeId),
                        new FunctionExecutionBinding.AdapterBinding(nextOpId(),
                            CaptureMode.SHARED_CELL,
                            new AdaptSourceRef.SharedCell(new BindingId(11), 0), F_II, F_IIS)),
                    ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "return boundary kind");
        }

        // (d) Callback rows: wrong kind for the invocation shape and a wrong
        //     boundary count.
        {
            OpId callbackOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(boundaryWith(rb, BoundaryKind.DEAL_TO_HOST, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(new ValueId(210), F_IIS,
                    List.of(pb), rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("d.callbackParameter.wrongKind", "d",
                SemanticIrValidator.validate(unit(Map.of(
                        new FunctionAllocationIdentity(210),
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(4),
                            new BlockId(4))), ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "HOST_TO_DEAL");
        }
        {
            OpId callbackOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.HOST_TO_DEAL, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(boundaryWith(rb, BoundaryKind.DEAL_TO_HOST, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callbackOp));
            ops.add(opWith(callbackOp, SemanticOpKind.CALLBACK_INVOKE,
                new KindPayload.CallbackInvokePayload(new ValueId(211), F_IIS,
                    List.of(pb), rb),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("d.callback.wrongParameterCount", "d",
                SemanticIrValidator.validate(unit(Map.of(
                        new FunctionAllocationIdentity(211),
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(5),
                            new BlockId(5))), ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "CALLBACK_INVOKE parameter boundaries (1) must match the descriptor "
                    + "parameters (2)");
        }

        // (e) Array cells: wrong policy and a boundary outside its parent.
        {
            OpId arrayOp = nextOpId();
            OpId elementBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(elementBoundary, BoundaryKind.ARRAY_LITERAL_ELEMENT, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, arrayOp));
            ops.add(opWith(arrayOp, SemanticOpKind.ARRAY_NEW,
                new KindPayload.ArrayNewPayload(INT, List.of(nextValue()),
                    List.of(elementBoundary)),
                nextValue(), ARRAY_INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("e.arrayLiteralElement.wrongPolicy", "e",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ARRAY_LITERAL_ELEMENT",
                "ARRAY_ELEMENT_DESCRIPTOR");
        }
        {
            OpId constOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(nextOpId(), BoundaryKind.ARRAY_ELEMENT_READ, INT,
                FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR, constOp));
            ops.add(opWith(constOp, SemanticOpKind.CONST,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("e.arrayElementRead.outsideParent", "e",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ARRAY_ELEMENT_READ",
                "outside an INDEX_READ");
        }
        {
            OpId assignOp = nextOpId();
            OpId assignBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(assignBoundary, BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT, INT,
                FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, assignOp));
            ops.add(opWith(assignOp, SemanticOpKind.ASSIGN,
                new KindPayload.AssignPayload(deal.semantic.ir.AssignTargetKind.VARIABLE,
                    List.of(nextOpId(), assignBoundary)),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("e.arrayElementAssignment.outsideParent", "e",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ARRAY_ELEMENT_ASSIGNMENT",
                "outside an ASSIGN ARRAY_SLOT chain");
        }

        // (f) External/stdlib cells: wrong policy for the kind.
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.HOST_PARAMETER, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.ExternalFunction(MOD_B, "f", F_IS,
                            ExternalExecutionOwner.RETAINED_ABI)),
                    F_IS, List.of(pb), rb, null, null, null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("f.externalParameter.wrongPolicy", "f",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "EXTERNAL_PARAMETER",
                "descriptor-kind rule");
        }
        {
            OpId stdlibOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.STDLIB_PARAMETER, INT,
                FailurePolicyId.FUNCTION_SIGNATURE, stdlibOp));
            ops.add(boundaryWith(rb, BoundaryKind.STDLIB_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, stdlibOp));
            ops.add(opWith(stdlibOp, SemanticOpKind.STDLIB_CALL,
                new KindPayload.StdlibCallPayload(StdlibFunctionId.MATH_ABS_INT,
                    List.of(nextValue()), SemanticCapability.STDLIB_SEMANTICS),
                nextValue(), INT, FailurePolicyId.INT32_RESULT, null));
            negative("f.stdlibParameter.wrongPolicy", "f",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "STDLIB_PARAMETER",
                "descriptor-kind rule");
        }

        // (g) EXTERNAL_ENTRY rows: descriptor mismatch on the sync return and
        //     wrong kind on the async return.
        {
            OpId entryOp = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS, false, rb,
                    null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("g.entrySync.returnDescriptorMismatch", "g",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "EXTERNAL_RETURN",
                "declared return descriptor");
        }
        {
            OpId entryOp = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IIS_ASYNC, true,
                    rb, STRING),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("g.entryAsync.wrongKind", "g",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "async EXTERNAL_ENTRY",
                "FUNCTION_RETURN");
        }

        // (h) ASYNC_START rows: completion-descriptor mismatch, a return
        //     boundary on a zero-return resolution, an outer adapter-over-async
        //     return boundary, a wrong parameter count, and a wrong parameter
        //     kind.
        {
            OpId startOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(pb), INT, rb,
                    null, null),
                new AsyncTokenId.Canonical(20, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("h.dealBody.completionDescriptorMismatch", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "FUNCTION_RETURN",
                "declared return descriptor");
        }
        {
            OpId startOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, startOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.RUN, List.of(pb), STRING, rb,
                    "op-3", null),
                new AsyncTokenId.Canonical(21, AsyncTokenOwner.HOST_OPERATION),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("h.asyncHost.returnBoundary", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ASYNC_START(HOST)",
                "zero return boundaries");
        }
        {
            OpId outerOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(opWith(outerOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.AdapterBinding(nextOpId(),
                            CaptureMode.SHARED_CELL,
                            new AdaptSourceRef.SharedCell(new BindingId(12), 0), F_II, F_IIS)),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(pb), STRING,
                    rb, null, null),
                new AsyncTokenId.Canonical(22, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("h.adapterOverAsync.outerReturnBoundary", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "zero return boundaries");
        }
        {
            OpId startOp = nextOpId();
            OpId pb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.HOST_PARAMETER, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.RUN, List.of(pb), STRING, null,
                    "op-4", null),
                new AsyncTokenId.Canonical(23, AsyncTokenOwner.HOST_OPERATION),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("h.asyncHost.wrongParameterCount", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "ASYNC_START parameter boundaries (1) must match the resolved signature "
                    + "parameters (2)");
        }
        {
            OpId startOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.DEAL_TO_HOST, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, startOp));
            ops.add(opWith(startOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(pb), INT, rb,
                    null, null),
                new AsyncTokenId.Canonical(24, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("h.dealBody.parameterWrongKind", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "FUNCTION_PARAMETER");
        }

        // (h) ELIDED_BY_ADAPTER placement (R-ELIDED-PLACEMENT): parented to a
        //     CALL, and parented to a non-adapter ASYNC_START.
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            OpId nestedOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IS, List.of(pb), rb, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(nestedOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.ELIDED_BY_ADAPTER, List.of(),
                    STRING, null, "op-5", null),
                new AsyncTokenId.Canonical(25, AsyncTokenOwner.HOST_OPERATION),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, callOp));
            negative("h.elided.parentedToCall", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_ELIDED_PLACEMENT, "ELIDED_BY_ADAPTER",
                "parented to CALL");
        }
        {
            OpId outerOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            OpId nestedOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, outerOp));
            ops.add(opWith(outerOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(pb), INT, rb,
                    null, null),
                new AsyncTokenId.Canonical(26, AsyncTokenOwner.DEAL_BODY_TASK),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(opWith(nestedOp, SemanticOpKind.ASYNC_START,
                new KindPayload.AsyncStartPayload(
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.HostFunction(MOD_HOST, "op", F_IIS_ASYNC)),
                    AsyncStartSource.HOST, ParameterBoundaryMode.ELIDED_BY_ADAPTER, List.of(),
                    STRING, null, "op-6", null),
                new AsyncTokenId.Canonical(27, AsyncTokenOwner.HOST_OPERATION),
                InternalResultType.INTERNAL_ASYNC, FailurePolicyId.NO_DEAL_FAILURE, outerOp));
            negative("h.elided.outerNotAdapter", "h",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_ELIDED_PLACEMENT, "ELIDED_BY_ADAPTER",
                "does not resolve to an AdapterBinding");
        }

        // (i) The completion cell: a stray completion boundary outside the
        //     AWAIT position, a completion boundary outside its parent, and a
        //     wrong completion policy.
        {
            OpId awaitOp = nextOpId();
            OpId completionBoundary = nextOpId();
            OpId strayBoundary = nextOpId();
            AsyncTokenId token = new AsyncTokenId.Canonical(28, AsyncTokenOwner.DEAL_BODY_TASK);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitOp));
            ops.add(boundaryWith(strayBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, awaitOp));
            ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(token, INT, completionBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("i.completion.outsideAwaitsPosition", "i",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ASYNC_COMPLETION",
                "single AWAIT completion position");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            OpId strayBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(strayBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.ASYNC_COMPLETION, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IS, List.of(pb), rb, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("i.completion.outsideParent", "i",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "ASYNC_COMPLETION",
                "single AWAIT completion position");
        }
        {
            OpId awaitOp = nextOpId();
            OpId completionBoundary = nextOpId();
            AsyncTokenId token = new AsyncTokenId.Canonical(29, AsyncTokenOwner.DEAL_BODY_TASK);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(completionBoundary, BoundaryKind.ASYNC_COMPLETION, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, awaitOp));
            ops.add(opWith(awaitOp, SemanticOpKind.AWAIT,
                new KindPayload.AwaitPayload(token, INT, completionBoundary),
                nextValue(), INT, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("i.completion.wrongPolicy", "i",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "TYPE_DESCRIPTOR",
                "expected ASYNC_COMPLETION");
        }

        // (j) Zero-boundary shapes: a boundary parented to INTRINSIC_CALL,
        //     CLASS_FACTORY, and a stray boundary outside a CLASS_NEW field list.
        {
            OpId intrinsicOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(nextOpId(), BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, intrinsicOp));
            ops.add(opWith(intrinsicOp, SemanticOpKind.INTRINSIC_CALL,
                new KindPayload.IntrinsicCallPayload(IntrinsicKind.INT_CONVERT, nextValue()),
                nextValue(), INT, FailurePolicyId.INT_CONVERSION, null));
            negative("j.intrinsic.boundaryChild", "j",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "INTRINSIC_CALL",
                "zero boundary children");
        }
        {
            OpId factoryOp = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(nextOpId(), BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, factoryOp));
            ops.add(opWith(factoryOp, SemanticOpKind.CLASS_FACTORY,
                new KindPayload.ClassFactoryPayload(new ClassId("mod.a", "C"), List.of(),
                    nextOpId()),
                null, null, FailurePolicyId.CLASS_CONSTRUCTION, null));
            negative("j.classFactory.boundaryChild", "j",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "CLASS_FACTORY",
                "zero boundary children");
        }
        {
            ClassId classId = new ClassId("mod.a", "C");
            ClassLayout layout = new ClassLayout(classId,
                List.of(new ClassLayout.FieldLayout("f", INT, true, DefaultOwner.LOCAL)));
            OpId classNewOp = nextOpId();
            OpId literalBoundary = nextOpId();
            OpId strayBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(literalBoundary, BoundaryKind.CLASS_LITERAL_FIELD, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(boundaryWith(strayBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, classNewOp));
            ops.add(opWith(classNewOp, SemanticOpKind.CLASS_NEW,
                new KindPayload.ClassNewPayload(classId, layout,
                    List.of(new KindPayload.ProvidedField("f", nextValue())),
                    DefaultOwner.LOCAL, List.of(), null,
                    List.of(new KindPayload.FieldBoundary("f", BoundaryKind.CLASS_LITERAL_FIELD,
                        literalBoundary))),
                nextValue(), new RuntimeDescriptor.Class(classId),
                FailurePolicyId.CLASS_CONSTRUCTION, null));
            negative("j.classNew.strayBoundary", "j",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "CLASS_NEW field boundary");
        }

        // (k) The JSON row family: each exception cell with TYPE_DESCRIPTOR.
        negative("k.jsonFromField.wrongPolicy", "k", SemanticIrValidator.validate(
                unit(List.of(boundary(BoundaryKind.JSON_FROM_FIELD, STRING,
                    FailurePolicyId.TYPE_DESCRIPTOR, null))), FACTS),
            SemanticIrValidator.R_BOUNDARY_TRIPLE, "JSON_FROM_FIELD", "JSON_FROM_NULL",
            "TYPE_DESCRIPTOR");
        negative("k.jsonToField.wrongPolicy", "k", SemanticIrValidator.validate(
                unit(List.of(boundary(BoundaryKind.JSON_TO_FIELD, INT,
                    FailurePolicyId.TYPE_DESCRIPTOR, null))), FACTS),
            SemanticIrValidator.R_BOUNDARY_TRIPLE, "JSON_TO_FIELD", "JSON_TO_ERROR",
            "TYPE_DESCRIPTOR");

        // General call-family negatives: a parameter boundary outside the
        // invocation's parameter list, a descriptor mismatch, a wrong
        // parameter count, and the missing single return boundary.
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            OpId strayBoundary = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(strayBoundary, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IS, List.of(pb), rb, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("call.parameterOutsideList", "call",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "parameter/return lists");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IS, List.of(pb), rb, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("call.parameterDescriptorMismatch", "call",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "FUNCTION_PARAMETER boundary 0",
                "declared parameter descriptor");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.FUNCTION_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IIS, List.of(pb), rb, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("call.wrongParameterCount", "call",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "CALL parameter boundaries (1) must match the signature parameters (2)");
        }
        {
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(pb, BoundaryKind.FUNCTION_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.DIRECT,
                    new KindPayload.CallCallee.Static(
                        new FunctionExecutionBinding.LoweredBody(new FunctionId(1),
                            new BlockId(1))),
                    F_IS, List.of(pb), null, null, new BlockId(1), null),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("call.missingReturnBoundary", "call",
                SemanticIrValidator.validate(unit(ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE,
                "the CALL must carry its single return boundary");
        }
        {
            // A SHARED_BODY external CALL carrying a caller-side return
            // boundary (single unit: the entry lives in the same module).
            OpId entryOp = nextOpId();
            OpId entryReturn = nextOpId();
            OpId callOp = nextOpId();
            OpId pb = nextOpId();
            OpId rb = nextOpId();
            FunctionExecutionBinding.ExternalFunction binding =
                new FunctionExecutionBinding.ExternalFunction(MOD, "f", F_IS,
                    ExternalExecutionOwner.SHARED_BODY);
            List<SemanticOp> ops = new ArrayList<>();
            ops.add(boundaryWith(entryReturn, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, entryOp));
            ops.add(opWith(entryOp, SemanticOpKind.EXTERNAL_ENTRY,
                new KindPayload.ExternalEntryPayload("f", new FunctionId(1), F_IS, false,
                    entryReturn, null),
                null, null, FailurePolicyId.NO_DEAL_FAILURE, null));
            ops.add(boundaryWith(pb, BoundaryKind.EXTERNAL_PARAMETER, INT,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(boundaryWith(rb, BoundaryKind.EXTERNAL_RETURN, STRING,
                FailurePolicyId.TYPE_DESCRIPTOR, callOp));
            ops.add(opWith(callOp, SemanticOpKind.CALL,
                new KindPayload.CallPayload(CallMode.EXTERNAL,
                    new KindPayload.CallCallee.Static(binding),
                    F_IS, List.of(pb), rb, null, null, entryOp),
                nextValue(), STRING, FailurePolicyId.NO_DEAL_FAILURE, null));
            negative("call.sharedBody.callerSideReturn", "call",
                SemanticIrValidator.validate(unit(Map.of(new FunctionAllocationIdentity(303),
                    binding), ops), FACTS),
                SemanticIrValidator.R_BOUNDARY_TRIPLE, "SHARED_BODY",
                "no caller-side return boundary");
        }

        // Reserved boundary names (R-ENUM, the pinned invalid-IR injection
        // route; the typed closed enum cannot express a reserved name).
        for (String reserved : BoundaryKind.RESERVED_NAMES) {
            LoweredModuleUnit base = unit(List.of(
                boundary(BoundaryKind.VARIABLE_DECLARATION, STRING,
                    FailurePolicyId.TYPE_DESCRIPTOR, null)));
            assertPass(SemanticIrValidator.validate(base, FACTS),
                "reserved-boundary-name injection base (typed surface)");
            String text = substitutePayloadLeaf(SemanticIrValidator.toUnitText(base),
                "kind", "VARIABLE_DECLARATION", reserved);
            negative("reserved.boundaryName." + reserved, "reserved",
                SemanticIrValidator.validateText(text, FACTS),
                SemanticIrValidator.R_ENUM, reserved);
        }

        // Reserved policy names (R-RESERVED-NAME; the typed closed enum cannot
        // express a reserved name).
        for (String reserved : FailurePolicyId.RESERVED_NAMES) {
            LoweredModuleUnit base = unit(List.of(
                op(SemanticOpKind.BINARY,
                    new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null),
                    nextValue(), INT, FailurePolicyId.INT32_RESULT, null)));
            assertPass(SemanticIrValidator.validate(base, FACTS),
                "reserved-policy-name injection base (typed surface)");
            String text = substitutePolicy(SemanticIrValidator.toUnitText(base),
                "INT32_RESULT", reserved);
            negative("reserved.policyName." + reserved, "reserved",
                SemanticIrValidator.validateText(text, FACTS),
                SemanticIrValidator.R_RESERVED_NAME, reserved);
        }

        check(negativeRules.equals(new LinkedHashSet<>(List.of(
                SemanticIrValidator.R_BOUNDARY_TRIPLE, SemanticIrValidator.R_ENUM,
                SemanticIrValidator.R_RESERVED_NAME, SemanticIrValidator.R_ELIDED_PLACEMENT))),
            "the negative corpus asserts exactly the pinned first-failure rules "
                + "{R-BOUNDARY-TRIPLE, R-ENUM, R-RESERVED-NAME, R-ELIDED-PLACEMENT}; got "
                + negativeRules);
    }

    // =========================================================================
    // Text-surface substitution helpers (one leaf + digest recompute)
    // =========================================================================

    private static CanonicalJson.Obj parseObj(String text) {
        return (CanonicalJson.Obj) CanonicalJson.parse(text);
    }

    private static CanonicalJson.Value at(CanonicalJson.Obj obj, String key) {
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (entry.key().equals(key)) {
                return entry.value();
            }
        }
        return null;
    }

    private static CanonicalJson.Obj withEntry(CanonicalJson.Obj obj, String key,
            CanonicalJson.Value value) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            entries.add(entry.key().equals(key) ? CanonicalJson.e(key, value) : entry);
        }
        return CanonicalJson.obj(entries);
    }

    private static String recomputeContractDigest(CanonicalJson.Obj contract) {
        List<CanonicalJson.Entry> eight = new ArrayList<>();
        for (CanonicalJson.Entry entry : contract.entries()) {
            if (!"canonicalDigest".equals(entry.key())) {
                eight.add(entry);
            }
        }
        return CanonicalJson.sha256Hex(CanonicalJson.serializeBytes(CanonicalJson.obj(eight)));
    }

    private static CanonicalJson.Obj contractWith(CanonicalJson.Obj contract, String key,
            CanonicalJson.Value value) {
        CanonicalJson.Obj updated = withEntry(contract, key, value);
        String digest = recomputeContractDigest(updated);
        return withEntry(updated, "canonicalDigest", CanonicalJson.str(digest));
    }

    private static CanonicalJson.Obj firstOp(CanonicalJson.Obj root) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        return (CanonicalJson.Obj) ops.items().get(0);
    }

    private static CanonicalJson.Obj withOps(CanonicalJson.Obj root, CanonicalJson.Obj op) {
        CanonicalJson.Arr ops = (CanonicalJson.Arr) at(root, "ops");
        List<CanonicalJson.Value> items = new ArrayList<>(ops.items());
        items.set(0, op);
        return withEntry(root, "ops", CanonicalJson.arr(items));
    }

    private static String serialize(CanonicalJson.Value value) {
        return CanonicalJson.serializeText(value);
    }

    private static String substitutePolicy(String text, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "failurePolicy", CanonicalJson.str(to));
        CanonicalJson.Obj op2 = withEntry(op, "failurePolicy", CanonicalJson.str(to));
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    private static String substitutePayloadLeaf(String text, String key, String from, String to) {
        CanonicalJson.Obj root = parseObj(text);
        CanonicalJson.Obj op = firstOp(root);
        CanonicalJson.Obj payload = (CanonicalJson.Obj) at(op, "payload");
        CanonicalJson.Obj payload2 = withEntry(payload, key, CanonicalJson.str(to));
        CanonicalJson.Obj contract = (CanonicalJson.Obj) at(op, "contract");
        CanonicalJson.Obj contract2 = contractWith(contract, "payload", payload2);
        CanonicalJson.Obj op2 = withEntry(op, "payload", payload2);
        op2 = withEntry(op2, "contract", contract2);
        return serialize(withOps(root, op2));
    }

    // =========================================================================
    // 4. The executor closed-subset tie: the 13 non-BOUNDARY policies fail closed
    // =========================================================================

    /** The closed 11-policy executor subset (D3, exact). */
    private static final Set<FailurePolicyId> EXECUTABLE_POLICIES = new LinkedHashSet<>(List.of(
        FailurePolicyId.TYPE_DESCRIPTOR, FailurePolicyId.FUNCTION_SIGNATURE,
        FailurePolicyId.HOST_PARAMETER, FailurePolicyId.HOST_SYNC_RETURN,
        FailurePolicyId.ASYNC_COMPLETION, FailurePolicyId.ARRAY_ELEMENT_DESCRIPTOR,
        FailurePolicyId.ARRAY_READ_INDEX_THEN_DESCRIPTOR,
        FailurePolicyId.ARRAY_WRITE_BOUNDS_THEN_ELEMENT, FailurePolicyId.ARRAY_DELETE_BOUNDS,
        FailurePolicyId.JSON_FROM_NULL, FailurePolicyId.JSON_TO_ERROR,
        FailurePolicyId.BYTES_READ, FailurePolicyId.BYTES_WRITE));

    static void testExecutorClosedSubsetTie() {
        System.out.println("-- Executor closed-subset tie: the 14 non-executor policies fail closed --");

        check(FailurePolicyId.values().length == 27,
            "the policy universe is exactly 27 values");
        check(EXECUTABLE_POLICIES.size() == 13,
            "the executor subset is exactly 13 policies; got " + EXECUTABLE_POLICIES.size());
        BoundaryValueView stringView = BoundaryValueView.of(ActualKind.STRING);
        int refused = 0;
        for (FailurePolicyId policy : FailurePolicyId.values()) {
            if (EXECUTABLE_POLICIES.contains(policy)) {
                continue;
            }
            expectDefect(() -> BoundaryExecutor.check(policy, STRING, stringView,
                    BoundaryContext.none()),
                "check(" + policy.name() + ") outside the closed 11-policy subset");
            expectDefect(() -> BoundaryExecutor.execute(policy, STRING, stringView,
                    BoundaryContext.none(), new BoundaryRealization.RuntimeValidation("check")),
                "execute(" + policy.name() + ") outside the closed 11-policy subset");
            refused++;
        }
        check(refused == 14,
            "exactly the 14 non-executor policies are refused fail closed; got " + refused);

        // The out-of-table descriptor/policy pairings fail closed too (the
        // validator's rejection and the executor's Defect are the same tie).
        expectDefect(() -> BoundaryExecutor.check(FailurePolicyId.TYPE_DESCRIPTOR, F_IS,
                BoundaryValueView.ofFunction(F_IS), BoundaryContext.none()),
            "TYPE_DESCRIPTOR with a function descriptor (descriptor-kind rule assigns "
                + "FUNCTION_SIGNATURE)");
        expectDefect(() -> BoundaryExecutor.check(FailurePolicyId.FUNCTION_SIGNATURE, STRING,
                stringView, BoundaryContext.none()),
            "FUNCTION_SIGNATURE with a non-function descriptor (descriptor-kind rule assigns "
                + "TYPE_DESCRIPTOR)");
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Boundary Table Corpus Test (ISSUE-0366, wiki Verification 4) ===\n");

        testPreservationPins();
        List<Row> rows = positiveRows();
        testPositiveCorpus(rows);
        testPerModeBoundaryCounts(rows);
        testNegativeCorpus();
        testExecutorClosedSubsetTie();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
