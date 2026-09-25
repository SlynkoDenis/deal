package deal.test;

import deal.checker.CheckResult;
import deal.checker.ModuleResolver;
import deal.checker.ModuleResolver.ModuleNotFoundException;
import deal.checker.NameResolver;
import deal.checker.Symbol;
import deal.checker.SymbolTable;
import deal.checker.TypeChecker;
import deal.diagnostics.CompilerDiagnostic;
import deal.diagnostics.DiagnosticCode;
import deal.lexer.LexResult;
import deal.lexer.Lexer;
import deal.parser.ParseResult;
import deal.parser.Parser;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.DynamicResolutionKind;
import deal.semantic.ir.DynamicReturnBoundaryProtocol;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RawBinding;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * ISSUE-0673 — the closed
 * {@code FunctionExecutionBinding.DynamicFunctionValue(OpId, Func)} member,
 * its canonical and raw shapes, its exactly-one registry entry point, and
 * the closed shape-admission plus producing-op correlation clauses (wiki
 * {@code function-typed-value-materialization-and-dispatch} M1 and M3 items
 * 1-2; wiki {@code semantic-ir-construct-coverage-cutover} K9 item 4 and
 * K11).
 *
 * <p><b>The member.</b> The sealed set grows by exactly this one record and
 * carries the producing op id on the landed
 * {@code materializingBoundaryOpId} raw position; the canonical binding
 * object is
 * {@code {"descriptor": <canonical Func text>, "materializingBoundaryOpId":
 * <op-id object>, "type": "dynamicFunctionValue"}}. The record names no
 * execution class — the class is the runtime value's own producing
 * registration at execution — so
 * {@link DynamicReturnBoundaryProtocol#kindOf} fails closed on it.</p>
 *
 * <p><b>The registry.</b>
 * {@link FunctionBindingRegistry#registerDynamicFunctionValue} registers
 * under the landed exactly-one discipline: a duplicate key is rejected at
 * registration time, never overwritten.</p>
 *
 * <p><b>The closed gate.</b> {@code R-ENUM} admits the shape and requires a
 * non-null producing op id and descriptor; {@code R-FUNCTION-BINDING}
 * correlates the named op with the registration: the named op exists in
 * the unit, its result identity is the registration key, and its result
 * descriptor equals the registered descriptor. The closed operation-kind,
 * payload-record, boundary-kind, failure-policy, and schema-version sets
 * are unchanged.</p>
 *
 * <p><b>Anti-hollow.</b> The positive drive doctors a real lowered unit's
 * canonical text (the unit the validation-core entry produced from a
 * checked source) and validates it through the same text surface; every
 * negative seed is derived from that positive text by one mutation, so
 * each clause is load-bearing. No parallel validator or registry surface
 * exists.</p>
 */
public class DynamicFunctionValueBindingTest {

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

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new ExternalModuleInterface(MODULE,
                ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(),
                InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();
    private static final SemanticIrValidator.ComparisonFacts FACTS =
        new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);

    /** The checked source of the fixture: one function expression bound to a declaration. */
    private static final String SOURCE = """
        function main(): null {
          let f: (x: int) => null = function(x: int): null { };
        }
        """;

    private static ModuleResolver resolver() {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath, String importingModule,
                    Set<String> modulesInProgress) throws ModuleNotFoundException {
                throw new ModuleNotFoundException("Module not found: " + modulePath);
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                    String importingModule) {
                return null;
            }
        };
    }

    /** The real production lowering of {@link #SOURCE} through the validation-core entry. */
    private static LoweredModuleUnit loweredUnit() {
        LexResult lex = new Lexer(SOURCE, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), "the fixture source parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, resolver());
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), "the fixture source resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult checks = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(checks.diagnostics().isEmpty(), "the fixture source checks cleanly: "
            + checks.diagnostics());
        if (checks.hasErrors()) {
            return null;
        }
        SemanticLowerer.ValidationCoreResult lowering = SemanticLowerer.lowerModuleValidationCore(
            new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), parse.program(),
                checks, List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
        check(lowering != null && !lowering.lowering().hasErrors()
                && lowering.lowering().unit() != null,
            "the fixture source lowers through the validation-core entry to a validated "
                + "unit: " + (lowering == null ? "null" : lowering.lowering().diagnostics()));
        if (lowering == null || lowering.lowering().hasErrors()
                || lowering.lowering().unit() == null) {
            return null;
        }
        return lowering.lowering().unit();
    }

    /**
     * The doctoring fixture: the real unit, its canonical text, and the
     * function-expression closure facts the dynamic registration names.
     */
    private record Fixture(LoweredModuleUnit unit, String text, long closureKey,
                           OpId closureOp, String closureDescriptor, OpId otherClosureOp,
                           String otherClosureDescriptor) {
    }

    private static Fixture fixture() {
        LoweredModuleUnit unit = loweredUnit();
        if (unit == null) {
            return null;
        }
        SemanticOp closure = null;
        SemanticOp other = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() != SemanticOpKind.CLOSURE_NEW
                    || !(op.result() instanceof ValueId)) {
                continue;
            }
            RuntimeDescriptor.Func descriptor = (RuntimeDescriptor.Func) op.resultType();
            if (descriptor.paramTypes().size() == 1) {
                closure = op;
            } else {
                other = op;
            }
        }
        check(closure != null, "the fixture unit carries the function expression's "
            + "CLOSURE_NEW (the one-parameter closure)");
        check(other != null, "the fixture unit carries the entry closure's CLOSURE_NEW");
        if (closure == null || other == null) {
            return null;
        }
        long key = ((ValueId) closure.result()).id();
        check(unit.functionBindings().get(new FunctionAllocationIdentity(key))
                instanceof FunctionExecutionBinding.LoweredBody,
            "the function expression's produced allocation identity is registered as a "
                + "LoweredBody (the pre-doctoring state)");
        return new Fixture(unit, SemanticIrValidator.toUnitText(unit), key, closure.opId(),
            ((RuntimeDescriptor) closure.resultType()).canonicalSpecText(), other.opId(),
            ((RuntimeDescriptor) other.resultType()).canonicalSpecText());
    }

    // =========================================================================
    // 1. The member and the registry entry point
    // =========================================================================

    private static void testMemberAndRegistry() {
        System.out.println("-- the closed member and the registry entry point --");

        OpId producing = new OpId(MODULE, 29);
        RuntimeDescriptor.Func descriptor = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Null.INSTANCE);
        FunctionExecutionBinding binding =
            new FunctionExecutionBinding.DynamicFunctionValue(producing, descriptor);
        check(binding instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic
                && dynamic.materializingOpId().equals(producing)
                && dynamic.descriptor().equals(descriptor),
            "DynamicFunctionValue carries the producing op id and the descriptor");
        boolean nullOpRejected = false;
        try {
            new FunctionExecutionBinding.DynamicFunctionValue(null, descriptor);
        } catch (NullPointerException expected) {
            nullOpRejected = true;
        }
        check(nullOpRejected, "DynamicFunctionValue rejects a null producing op id");
        boolean nullDescriptorRejected = false;
        try {
            new FunctionExecutionBinding.DynamicFunctionValue(producing, null);
        } catch (NullPointerException expected) {
            nullDescriptorRejected = true;
        }
        check(nullDescriptorRejected, "DynamicFunctionValue rejects a null descriptor");

        Set<Class<?>> permitted = Set.copyOf(Arrays.asList(
            FunctionExecutionBinding.class.getPermittedSubclasses()));
        check(permitted.equals(Set.of(
                FunctionExecutionBinding.LoweredBody.class,
                FunctionExecutionBinding.AdapterBinding.class,
                FunctionExecutionBinding.HostFunction.class,
                FunctionExecutionBinding.HostFunctionValue.class,
                FunctionExecutionBinding.ExternalFunction.class,
                FunctionExecutionBinding.IntrinsicFunction.class,
                FunctionExecutionBinding.DynamicFunctionValue.class)),
            "the sealed set is exactly the seven pinned variants; got " + permitted);

        // The record names no execution class: the resolution protocol fails
        // closed on it (the class is the runtime value's producing
        // registration at execution).
        boolean kindOfRejected = false;
        try {
            DynamicReturnBoundaryProtocol.kindOf(binding);
        } catch (IllegalArgumentException expected) {
            kindOfRejected = true;
        }
        check(kindOfRejected, "kindOf fails closed on a DynamicFunctionValue (the record "
            + "names no execution class)");
        check(DynamicReturnBoundaryProtocol.kindOf(
                new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                    IntrinsicKind.INT_CONVERT.declaredSignature()))
                == DynamicResolutionKind.HOST,
            "the pre-existing intrinsic classification is unchanged");

        // The registry entry point: exactly one registration per producing
        // allocation, duplicate keys rejected at registration time.
        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(29);
        registry.registerDynamicFunctionValue(identity, producing, descriptor);
        check(registry.size() == 1, "one registration is recorded; got " + registry.size());
        FunctionExecutionBinding registered = registry.bindings().get(identity);
        check(registered instanceof FunctionExecutionBinding.DynamicFunctionValue dynamic
                && dynamic.materializingOpId().equals(producing)
                && dynamic.descriptor().equals(descriptor),
            "the registration is the DynamicFunctionValue record with the given producing "
                + "op id and descriptor; got " + registered);
        boolean duplicateRejected = false;
        try {
            registry.registerDynamicFunctionValue(identity, producing, descriptor);
        } catch (IllegalStateException expected) {
            duplicateRejected = true;
        }
        check(duplicateRejected, "a duplicate-key registration is rejected at registration "
            + "time (never overwritten)");
        check(registry.size() == 1, "the rejected duplicate left exactly one registration");
        boolean unmodifiable = false;
        try {
            registry.bindings().put(new FunctionAllocationIdentity(41), binding);
        } catch (UnsupportedOperationException expected) {
            unmodifiable = true;
        }
        check(unmodifiable, "the registration snapshot stays unmodifiable");
        boolean nullIdentityRejected = false;
        try {
            registry.registerDynamicFunctionValue(null, producing, descriptor);
        } catch (NullPointerException expected) {
            nullIdentityRejected = true;
        }
        check(nullIdentityRejected, "the registry entry point rejects a null identity");
    }

    // =========================================================================
    // 2. The canonical and raw shapes and the byte-identical round trip
    // =========================================================================

    private static void testCanonicalShapes(Fixture fixture) {
        System.out.println("-- canonical/raw shapes and the byte-identical round trip --");

        OpId producing = fixture.closureOp();
        RuntimeDescriptor.Func descriptor = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.Null.INSTANCE);
        check(descriptor.canonicalSpecText().equals(fixture.closureDescriptor()),
            "the fixture closure's descriptor is " + descriptor.canonicalSpecText()
                + "; got " + fixture.closureDescriptor());

        // The typed binding renderer (the op-payload direction).
        CanonicalJson.Value typedJson = ContractSnapshotCanonicalizer.bindingJson(
            new FunctionExecutionBinding.DynamicFunctionValue(producing, descriptor));
        String typedText = ContractSnapshotCanonicalizer.serializeText(typedJson);
        check(typedText.contains("\"type\":\"dynamicFunctionValue\""),
            "the typed binding renderer carries the shape tag; got " + typedText);
        check(typedText.contains("\"materializingBoundaryOpId\":{\"id\":"),
            "the typed binding renderer carries the producing op id; got " + typedText);
        check(typedText.contains("\"descriptor\":\""
                + descriptor.canonicalSpecText() + "\""),
            "the typed binding renderer carries the descriptor; got " + typedText);

        // The raw binding rendering (the text direction) is the unit text
        // below: the raw renderer emits the same pinned binding object.
        String dynamic = withDynamicBinding(fixture);
        check(dynamic.contains(typedText),
            "the raw unit text carries the pinned binding object the typed renderer "
                + "produces; got " + dynamic);
        check(dynamic.contains("\"allocationId\":" + fixture.closureKey()
                + ",\"binding\":" + typedText),
            "the raw functionBindings entry carries the key and the pinned binding object");

        // The positive doctored unit text: canonical -> raw -> canonical.
        RawUnit decoded = ContractSnapshotCanonicalizer.parseUnit(
            (CanonicalJson.Obj) ContractSnapshotCanonicalizer.parseValidationText(dynamic));
        String reRendered = CanonicalJson.serializeText(
            ContractSnapshotCanonicalizer.toJson(decoded));
        check(dynamic.equals(reRendered),
            "the canonical text of a unit carrying one dynamicFunctionValue registration "
                + "round-trips byte-identically through parse and re-render");
        boolean carried = false;
        for (RawBinding entry : decoded.bindings()) {
            if ("dynamicFunctionValue".equals(entry.shape())) {
                carried = entry.allocationId() == fixture.closureKey()
                    && producing.equals(entry.materializingBoundaryOpId())
                    && descriptor.canonicalSpecText().equals(entry.descriptor())
                    && entry.modulePath() == null && entry.intrinsicKind() == null;
            }
        }
        check(carried, "the decoded raw binding carries the key, the producing op id on the "
            + "materializingBoundaryOpId position, and the descriptor text");
        check(dynamic.contains("\"type\":\"dynamicFunctionValue\""),
            "the unit text carries the dynamicFunctionValue shape tag");
    }

    // =========================================================================
    // 3. The closed gate: shape admission and producing-op correlation
    // =========================================================================

    private static void testClosedGatePositive(Fixture fixture) {
        System.out.println("-- closed gate: the correlated registration is admitted --");

        check(SemanticIrValidator.validate(fixture.unit(), FACTS).isEmpty(),
            "the unmutated fixture unit passes the closed 14 rules");
        check(SemanticIrValidator.validateText(fixture.text(), FACTS).isEmpty(),
            "the unmutated fixture text passes the closed 14 rules");

        String dynamic = withDynamicBinding(fixture);
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validateText(dynamic, FACTS);
        check(failure.isEmpty(), "a unit whose dynamicFunctionValue registration names its "
            + "producing op, result identity, and result descriptor passes the closed gate; "
            + "got " + failure.map(CompilerDiagnostic::message).orElse("admission"));

        // The raw model of the mutated text carries exactly one
        // dynamicFunctionValue entry.
        RawUnit decoded = ContractSnapshotCanonicalizer.parseUnit(
            (CanonicalJson.Obj) ContractSnapshotCanonicalizer.parseValidationText(dynamic));
        int dynamicBindings = 0;
        for (RawBinding entry : decoded.bindings()) {
            if ("dynamicFunctionValue".equals(entry.shape())) {
                dynamicBindings++;
            }
        }
        check(dynamicBindings == 1, "the doctored unit carries exactly one "
            + "dynamicFunctionValue registration; got " + dynamicBindings);
    }

    // =========================================================================
    // 4. The negative seeds of the shape and correlation clauses
    // =========================================================================

    private static void testNegativeSeeds(Fixture fixture) {
        System.out.println("-- negative seeds: the shape premise and the correlation --");

        String dynamic = withDynamicBinding(fixture);

        // (1) The producing op id absent (JSON null).
        String nullOp = withBinding(dynamic, fixture.closureKey(),
            b -> withEntry(b, "materializingBoundaryOpId", CanonicalJson.nullValue()));
        assertRule("a registration with a null producing op id", nullOp, "R-ENUM",
            "carries no producing op id and descriptor text");
        RawUnit nullOpRaw = ContractSnapshotCanonicalizer.parseUnit(
            (CanonicalJson.Obj) ContractSnapshotCanonicalizer.parseValidationText(nullOp));
        check(nullOpRaw.bindings().stream().anyMatch(b ->
                "dynamicFunctionValue".equals(b.shape()) && b.materializingBoundaryOpId() == null),
            "the raw model carries the absent producing-op position as null (the "
                + "transport never invents a value)");

        // (2) The producing op id key absent entirely.
        String droppedOp = withBinding(dynamic, fixture.closureKey(),
            b -> withoutEntry(b, "materializingBoundaryOpId"));
        assertRule("a registration whose producing-op position is absent", droppedOp,
            "R-ENUM", "carries no producing op id and descriptor text");

        // (3) The descriptor absent (JSON null).
        String nullDescriptor = withBinding(dynamic, fixture.closureKey(),
            b -> withEntry(b, "descriptor", CanonicalJson.nullValue()));
        assertRule("a registration with a null descriptor", nullDescriptor, "R-ENUM",
            "carries no producing op id and descriptor text");

        // (4) The descriptor position absent entirely.
        String droppedDescriptor = withBinding(dynamic, fixture.closureKey(),
            b -> withoutEntry(b, "descriptor"));
        assertRule("a registration whose descriptor position is absent",
            droppedDescriptor, "R-ENUM",
            "carries no producing op id and descriptor text");

        // (5) The named producing op absent from the unit.
        OpId dangling = new OpId(MODULE, 9999);
        String danglingText = withBinding(dynamic, fixture.closureKey(),
            b -> withEntry(b, "materializingBoundaryOpId",
                ContractSnapshotCanonicalizer.semanticIdJson(dangling)));
        assertRule("a registration naming an op absent from the unit", danglingText,
            "R-FUNCTION-BINDING", "does not resolve to an op of the unit");

        // (6) The named op's result identity not the registration key.
        String wrongKey = withBinding(dynamic, fixture.closureKey(),
            b -> withEntry(b, "materializingBoundaryOpId",
                ContractSnapshotCanonicalizer.semanticIdJson(fixture.otherClosureOp())));
        assertRule("a registration whose named op's result identity is not the key",
            wrongKey, "R-FUNCTION-BINDING",
            "does not carry the registered allocation identity as its result");

        // (7) The named op's result descriptor differing from the registered one.
        String descriptorMismatch = withBinding(dynamic, fixture.closureKey(),
            b -> withEntry(b, "descriptor",
                CanonicalJson.str(fixture.otherClosureDescriptor())));
        assertRule("a registration whose descriptor differs from the producing op's result "
            + "descriptor", descriptorMismatch, "R-FUNCTION-BINDING",
            "descriptor does not equal its producing op's result descriptor");

        // The positive control: the unmutated registration is admitted while
        // each single-field mutation above fails.
        check(SemanticIrValidator.validateText(dynamic, FACTS).isEmpty(),
            "the positive control (the correlated registration) stays admitted");
    }

    // =========================================================================
    // 5. The static-callee position stays closed
    // =========================================================================

    /**
     * A minimal unit whose single {@code CALL} names the given binding in the
     * nested {@code CallCallee.Static} position (the closed nested shape
     * enumeration is the same one every static callee passes).
     */
    private static LoweredModuleUnit withStaticCallee(FunctionExecutionBinding binding) {
        OpId callOp = new OpId(MODULE, 90);
        KindPayload payload = new KindPayload.CallPayload(CallMode.INDIRECT,
            new KindPayload.CallCallee.Static(binding),
            new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE),
            List.of(), null, null, null, null);
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, SemanticOpKind.CALL, null, List.of(), null,
            payload, FailurePolicyId.NO_DEAL_FAILURE, List.of(), "placeholder");
        contract = new OperationContractSnapshot(OperationContractSnapshot.VERSION,
            SemanticOpKind.CALL, null, List.of(), null, payload,
            FailurePolicyId.NO_DEAL_FAILURE, List.of(),
            ContractSnapshotCanonicalizer.digest(contract));
        SemanticOp call = new SemanticOp(callOp, SemanticOpKind.CALL,
            new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
                SourceOriginKind.SYNTHETIC, new AnchorId(0), null),
            new ValueId(90), null, List.of(), List.of(), payload,
            FailurePolicyId.NO_DEAL_FAILURE, contract);
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MODULE, INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH),
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(),
            Map.of(), List.of(call));
    }

    private static void testStaticCalleePosition() {
        System.out.println("-- the static-callee position stays closed --");

        FunctionExecutionBinding dynamic = new FunctionExecutionBinding.DynamicFunctionValue(
            new OpId(MODULE, 90),
            new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE));
        Optional<CompilerDiagnostic> failure =
            SemanticIrValidator.validate(withStaticCallee(dynamic), FACTS);
        check(failure.isPresent(), "a DynamicFunctionValue named inline in a static CALLEE "
            + "position fails the closed gate (the nested shape enumeration admits it "
            + "nowhere: a dynamic registration is a Dynamic-arm callee only)");
        if (failure.isPresent()) {
            String message = failure.get().message();
            String[] byRule = message.split("validatorRule ");
            check(byRule.length == 2 && byRule[1].startsWith("R-ENUM,"),
                "the static-callee rejection is named as R-ENUM; got \"" + message + "\"");
            check(message.contains("in a closed FunctionExecutionBinding shape position"),
                "the static-callee rejection names the closed shape position; got \""
                    + message + "\"");
        }
    }

    // =========================================================================
    // 6. The unchanged closed sets
    // =========================================================================

    private static void testUnchangedClosedSets() {
        System.out.println("-- the unchanged closed sets --");

        check("deal.semantic-ir/1".equals(LoweredModuleUnit.FORMAT_VERSION),
            "the deal.semantic-ir/1 version text is unchanged");
        check(SemanticOpKind.values().length == 55,
            "the closed SemanticOpKind set stays at 55 members; got "
                + SemanticOpKind.values().length);
        Map<String, Integer> shapes = new LinkedHashMap<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            shapes.merge(kind.payloadClass().getSimpleName(), 1, Integer::sum);
        }
        check(shapes.size() == 55, "the 55 closed kinds keep their 55 distinct payload "
            + "records; got " + shapes.size());
        check(new FunctionExecutionBinding.DynamicFunctionValue(
                new OpId(MODULE, 1),
                new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE))
                instanceof FunctionExecutionBinding.DynamicFunctionValue,
            "the new binding shape is a record of the closed sealed set (no payload record "
                + "and no op kind was added)");
    }

    // =========================================================================
    // Text-surface doctoring helpers
    // =========================================================================

    /** Replaces the fixture closure's LoweredBody entry with the dynamic registration. */
    private static String withDynamicBinding(Fixture fixture) {
        return withBinding(fixture.text(), fixture.closureKey(),
            b -> CanonicalJson.obj(
                CanonicalJson.e("descriptor", CanonicalJson.str(fixture.closureDescriptor())),
                CanonicalJson.e("materializingBoundaryOpId",
                    ContractSnapshotCanonicalizer.semanticIdJson(fixture.closureOp())),
                CanonicalJson.e("type", CanonicalJson.str("dynamicFunctionValue"))));
    }

    /** Rewrites one functionBindings entry's binding object, keyed by allocationId. */
    private static String withBinding(String text, long allocationId,
            java.util.function.UnaryOperator<CanonicalJson.Obj> rewrite) {
        CanonicalJson.Obj root = (CanonicalJson.Obj) CanonicalJson.parse(text);
        CanonicalJson.Arr bindings = (CanonicalJson.Arr) at(root, "functionBindings");
        List<CanonicalJson.Value> items = new ArrayList<>();
        for (CanonicalJson.Value item : bindings.items()) {
            CanonicalJson.Obj entry = (CanonicalJson.Obj) item;
            CanonicalJson.Value idValue = at(entry, "allocationId");
            if (idValue instanceof CanonicalJson.Int i && i.value() == allocationId) {
                CanonicalJson.Obj binding = (CanonicalJson.Obj) at(entry, "binding");
                entry = withEntry(entry, "binding", rewrite.apply(binding));
            }
            items.add(entry);
        }
        return CanonicalJson.serializeText(
            withEntry(root, "functionBindings", CanonicalJson.arr(items)));
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

    private static CanonicalJson.Obj withoutEntry(CanonicalJson.Obj obj, String key) {
        List<CanonicalJson.Entry> entries = new ArrayList<>();
        for (CanonicalJson.Entry entry : obj.entries()) {
            if (!entry.key().equals(key)) {
                entries.add(entry);
            }
        }
        return CanonicalJson.obj(entries);
    }

    private static void assertRule(String what, String text, String rule,
            String... contains) {
        Optional<CompilerDiagnostic> failure = SemanticIrValidator.validateText(text, FACTS);
        check(failure.isPresent(), what + " fails the closed gate");
        if (failure.isEmpty()) {
            return;
        }
        CompilerDiagnostic diagnostic = failure.get();
        check("E6005".equals(diagnostic.code()), what + " is rejected with E6005");
        check(diagnostic.diagnosticCode() == DiagnosticCode.E6005,
            what + " carries the canonical E6005 code");
        String message = diagnostic.message();
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the validator rule " + rule + "; got \"" + message + "\"");
        for (String fragment : contains) {
            check(message.contains(fragment),
                what + " message contains \"" + fragment + "\"; got \"" + message + "\"");
        }
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Dynamic Function Value Binding / Closed Shapes Test "
            + "(ISSUE-0673) ===\n");

        testMemberAndRegistry();
        Fixture fixture = fixture();
        if (fixture == null) {
            fail("the doctoring fixture could not be built");
        } else {
            testCanonicalShapes(fixture);
            testClosedGatePositive(fixture);
            testNegativeSeeds(fixture);
        }
        testUnchangedClosedSets();
        testStaticCalleePosition();

        System.out.println("\nDynamic function value binding: " + passed + " passed, "
            + failed + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
