package deal.test;

import deal.ast.ProgramNode;
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
import deal.semantic.BindingsProductionValidator;
import deal.semantic.CapabilityRegistry;
import deal.semantic.CheckedModuleInput;
import deal.semantic.CheckedModuleKind;
import deal.semantic.FunctionBindingRegistry;
import deal.semantic.SemanticLowerer;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CanonicalJson;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ContractSnapshotCanonicalizer;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContextHash;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.RawBinding;
import deal.semantic.ir.RawUnit;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticIdAllocator;
import deal.semantic.ir.SemanticIrDumper;
import deal.semantic.ir.SemanticIrValidator;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;
import deal.types.Type;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The intrinsic seed registrations and the closed bindings-gate admission
 * (ISSUE-0632; wiki {@code project-lowering-entry-and-registration-seeds}
 * D7/D13 and the registration-seed contract; wiki
 * {@code semantic-ir-construct-coverage-cutover} K9 item 7 and K14's
 * registration half).
 *
 * <p><b>Registration.</b> The two producer-less conversion intrinsics
 * ({@code int}/{@code number}) carry exactly one closed
 * {@code FunctionExecutionBinding.IntrinsicFunction {kind, descriptor}}
 * registration per intrinsic, keyed by the seeded function-value identity
 * the intrinsic binding's single {@code BINDING_INIT} carries as its init
 * operand, with the intrinsic's declared signature ({@code INT_CONVERT} is
 * {@code (number) -> int}, {@code NUMBER_CONVERT} is
 * {@code (int) -> number}). The registrations are recorded in the unit's
 * {@code functionBindings} and are dump-visible and re-readable: the shape
 * tag {@code intrinsicFunction} carries the kind and the descriptor text
 * through the typed-to-raw converter, the raw binding record, and both text
 * codec directions.</p>
 *
 * <p><b>Gate admission.</b> {@code REGISTRY_ONE_TO_ONE} admits a seeded key
 * exactly when the unit carries exactly one seed {@code BINDING_INIT} whose
 * init operand is that key and the key contributes no other producing
 * position; every {@code BINDING_INIT} whose init operand identity is the
 * result of no op of the unit must be keyed by exactly one
 * {@code IntrinsicFunction} registration and must not be a
 * {@code HOST_TO_DEAL} crossing input; the {@code (kind, descriptor)} pair
 * must equal the kind's pinned declared signature. R-FUNCTION-BINDING is
 * unaffected (the seeded key is not an op result). The nested static-callee
 * shape enumeration admits the {@code intrinsicFunction} shape since
 * ISSUE-0679 — the design's {@code CallCallee.Static(IntrinsicFunction)}
 * payload is the indirect intrinsic call's arm — while the shape position
 * keeps its closed discipline (the kind resolves in the closed
 * {@code IntrinsicKind} set and both the kind and the descriptor positions
 * are present); a doctored nested payload violating either still fails
 * R-ENUM.</p>
 *
 * <p><b>Anti-hollow.</b> Every assertion reads the produced unit's typed
 * {@code functionBindings} and the {@link SemanticIrDumper} dump; the shape
 * round-trips through the typed-to-raw conversion, the unit text mapping,
 * the text decode, and the typed binding renderer. No parallel
 * registration surface exists.</p>
 */
public class IntrinsicSeedBindingsTest {

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
    // Fixed invocation facts and source drivers
    // =========================================================================

    private static final ModuleId MODULE = new ModuleId("main");
    private static final String SOURCE_ID = "test.deal";
    private static final String REGISTRY_HASH =
        CapabilityRegistry.releaseRegistry().capabilityRegistryHash();
    private static final String INTERFACE_HASH = new ProjectInterfaceIndex(
        ProjectInterfaceIndex.FORMAT_VERSION, Map.of(MODULE,
            new deal.semantic.ir.ExternalModuleInterface(MODULE,
                deal.semantic.ir.ExternalModuleKind.IMPLEMENTATION,
                List.of(), List.of(), List.of(),
                deal.semantic.ir.InitializationMode.ONCE_AFTER_DEPENDENCIES)))
        .interfaceIndexDigest();

    private record CheckedSlice(ProgramNode program, CheckResult checks) {
    }

    /** A resolver serving the given fixed module export maps. */
    private static ModuleResolver resolver(Map<String, Map<String, Type>> exportsByModule) {
        return new ModuleResolver() {
            @Override
            public Map<String, Type> resolveModule(String modulePath, String importingModule,
                    Set<String> modulesInProgress) throws ModuleNotFoundException {
                Map<String, Type> exports = exportsByModule.get(modulePath);
                if (exports == null) {
                    throw new ModuleNotFoundException("Module not found: " + modulePath);
                }
                return exports;
            }

            @Override
            public Symbol.ClassSymbol resolveClassSymbol(String className, String modulePath,
                    String importingModule) throws ModuleNotFoundException {
                return null;
            }
        };
    }

    private static CheckedSlice checkSlice(String source, String what) {
        LexResult lex = new Lexer(source, SOURCE_ID).tokenize();
        ParseResult parse = new Parser(lex.tokens(), SOURCE_ID, lex.directiveEvents()).parse();
        check(parse.diagnostics().isEmpty(), what + ": the slice parses cleanly: "
            + parse.diagnostics());
        if (!parse.diagnostics().isEmpty()) {
            return null;
        }
        NameResolver nr = new NameResolver(SOURCE_ID, resolver(Map.of("lib.math", Map.of())));
        SymbolTable symTable = nr.resolve(parse.program());
        check(nr.diagnostics().isEmpty(), what + ": the slice resolves cleanly: "
            + nr.diagnostics());
        if (!nr.diagnostics().isEmpty()) {
            return null;
        }
        CheckResult result = TypeChecker.check(SOURCE_ID, symTable, nr, parse.program());
        check(result.diagnostics().isEmpty(), what + ": the slice checks cleanly: "
            + result.diagnostics());
        if (result.hasErrors()) {
            return null;
        }
        return new CheckedSlice(parse.program(), result);
    }

    private static CheckedModuleInput moduleOf(CheckedSlice slice) {
        return new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), slice.program(),
            slice.checks(), List.of(), List.of(), CheckedModuleKind.IMPLEMENTATION);
    }

    /** The resolved import facts of one checked program (compiled modules). */
    private static List<deal.semantic.ir.ResolvedImport> importsOf(ProgramNode program) {
        List<deal.semantic.ir.ResolvedImport> imports = new ArrayList<>();
        for (deal.ast.StatementNode stmt : program.statements()) {
            if (stmt instanceof deal.ast.ImportDeclaration imp) {
                imports.add(new deal.semantic.ir.ResolvedImport(imp.alias(), imp.modulePath(),
                    new ModuleId(imp.modulePath()),
                    deal.semantic.ir.ExternalModuleKind.IMPLEMENTATION));
            }
        }
        return imports;
    }

    /** One module's lowering through the validation-core entry (the B9-certifying entry). */
    private static SemanticLowerer.ValidationCoreResult lower(String source, String what) {
        CheckedSlice slice = checkSlice(source, what);
        if (slice == null) {
            return null;
        }
        return SemanticLowerer.lowerModuleValidationCore(moduleOf(slice),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)));
    }

    /** A lowered, closed-gate-validated unit for the named test. */
    private static SemanticLowerer.ValidationCoreResult validUnit(String source, String what) {
        SemanticLowerer.ValidationCoreResult result = lower(source, what);
        if (result == null) {
            return null;
        }
        check(result.lowering() != null && !result.lowering().hasErrors()
                && result.lowering().unit() != null,
            what + " lowers through the validation-core entry to a validated unit: "
                + (result.lowering() == null ? "null" : result.lowering().diagnostics()));
        if (result.lowering() == null || result.lowering().hasErrors()
                || result.lowering().unit() == null) {
            return null;
        }
        return result;
    }

    private static SemanticIrValidator.ComparisonFacts comparisonFacts() {
        return new SemanticIrValidator.ComparisonFacts(INTERFACE_HASH,
            SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH);
    }

    // =========================================================================
    // 1. The typed unit and the dump carry exactly one IntrinsicFunction per
    //    conversion intrinsic, keyed by the seed BINDING_INIT's operand
    // =========================================================================

    private static void testSeedRegistrationsTypedAndDump() {
        System.out.println("-- the typed unit and the dump: one IntrinsicFunction per "
            + "conversion intrinsic, keyed by the seed init operand --");

        SemanticLowerer.ValidationCoreResult result = validUnit(
            "function main(): null { let a: int = 1; }", "the intrinsic-seed slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();

        // Exactly one IntrinsicFunction registration per conversion intrinsic.
        Map<FunctionAllocationIdentity, FunctionExecutionBinding.IntrinsicFunction> intrinsic =
            new LinkedHashMap<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction value) {
                intrinsic.put(entry.getKey(), value);
            }
        }
        check(intrinsic.size() == 2, "the unit carries exactly one IntrinsicFunction "
            + "registration per conversion intrinsic; got " + intrinsic.size());
        for (IntrinsicKind kind : IntrinsicKind.values()) {
            List<Map.Entry<FunctionAllocationIdentity,
                FunctionExecutionBinding.IntrinsicFunction>> matches = new ArrayList<>();
            for (Map.Entry<FunctionAllocationIdentity,
                    FunctionExecutionBinding.IntrinsicFunction> entry : intrinsic.entrySet()) {
                if (entry.getValue().kind() == kind) {
                    matches.add(entry);
                }
            }
            check(matches.size() == 1, "exactly one " + kind + " registration; got "
                + matches.size());
            if (matches.size() != 1) {
                continue;
            }
            RuntimeDescriptor.Func descriptor = matches.get(0).getValue().descriptor();
            check(descriptor.equals(kind.declaredSignature()),
                kind + " carries the pinned declared signature as a descriptor record; got "
                    + descriptor.canonicalSpecText());
            String expectedText = switch (kind) {
                case INT_CONVERT -> "(number)->int";
                case NUMBER_CONVERT -> "(int)->number";
            };
            check(descriptor.canonicalSpecText().equals(expectedText),
                kind + "'s declared signature text is " + expectedText + "; got "
                    + descriptor.canonicalSpecText());
        }

        // The key is the seeded function-value identity: the operand of the
        // intrinsic binding's single BINDING_INIT, and exactly one such init.
        for (String name : List.of("int", "number")) {
            IntrinsicKind kind = name.equals("int") ? IntrinsicKind.INT_CONVERT
                : IntrinsicKind.NUMBER_CONVERT;
            SemanticLowerer.BindingCoreBinding binding =
                bindingFact(result.bindingFacts(), name);
            check(binding != null, "the intrinsic binding '" + name + "' is registered by "
                + "the walk");
            if (binding == null) {
                continue;
            }
            List<SemanticOp> inits = new ArrayList<>();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BINDING_INIT
                        && op.payload() instanceof KindPayload.BindingInitPayload init
                        && init.binding().equals(binding.binding())) {
                    inits.add(op);
                }
            }
            check(inits.size() == 1, "the intrinsic binding '" + name + "' carries exactly "
                + "one BINDING_INIT; got " + inits.size());
            if (inits.size() != 1) {
                continue;
            }
            ValueId seeded = ((KindPayload.BindingInitPayload) inits.get(0).payload()).value();
            FunctionAllocationIdentity key = new FunctionAllocationIdentity(seeded.id());
            FunctionExecutionBinding registered = unit.functionBindings().get(key);
            check(registered instanceof FunctionExecutionBinding.IntrinsicFunction value
                    && value.kind() == kind,
                "the '" + name + "' binding's seed init operand " + seeded + " is the "
                    + kind + " registration key; got " + registered);
            // The seeded identity is the result of no op of the unit: the seed
            // BINDING_INIT is its only producing position.
            int producingOps = 0;
            for (SemanticOp op : unit.ops()) {
                if (op.result() instanceof ValueId value && value.id() == seeded.id()) {
                    producingOps++;
                }
            }
            check(producingOps == 0, "no op of the unit produces the seeded identity "
                + seeded + " (the seed init is the key's producing position); got "
                + producingOps + " producing op(s)");
        }

        // The dump records the registrations with their kind and descriptor,
        // and the canonical text maps exactly the typed registrations.
        String dump = SemanticIrDumper.dumpModuleText(unit);
        check(dump.split("\"type\":\"intrinsicFunction\"", -1).length - 1 == 2,
            "the unit dump records exactly two intrinsicFunction bindings");
        for (IntrinsicKind kind : IntrinsicKind.values()) {
            String expectedText = kind.declaredSignature().canonicalSpecText();
            check(dump.contains("\"intrinsicKind\":\"" + kind.name() + "\""),
                "the dump carries the intrinsic kind " + kind);
            check(dump.contains("{\"descriptor\":\"" + expectedText
                    + "\",\"intrinsicKind\":\"" + kind.name()
                    + "\",\"type\":\"intrinsicFunction\"}"),
                "the dump carries the closed intrinsicFunction binding object of " + kind);
        }
    }

    private static SemanticLowerer.BindingCoreBinding bindingFact(
            SemanticLowerer.BindingCoreFacts facts, String name) {
        for (SemanticLowerer.BindingCoreBinding binding : facts.bindings()) {
            if (binding.name().equals(name)) {
                return binding;
            }
        }
        return null;
    }

    // =========================================================================
    // 2. The codec directions: typed-to-raw, the unit text mapping, the text
    //    decode, and the typed binding renderer
    // =========================================================================

    private static void testCodecRoundTrip() {
        System.out.println("-- codec directions: typed -> raw -> text -> raw --");

        SemanticLowerer.ValidationCoreResult result = validUnit(
            "function main(): null { let a: int = 1; }", "the codec round-trip slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();

        // Direction 1: the typed-to-raw converter's exhaustive switch.
        RawUnit raw = RawUnit.fromTyped(unit);
        Map<String, RawBinding> rawIntrinsic = new LinkedHashMap<>();
        for (RawBinding binding : raw.bindings()) {
            if ("intrinsicFunction".equals(binding.shape())) {
                rawIntrinsic.put(binding.intrinsicKind(), binding);
            }
        }
        check(rawIntrinsic.size() == 2, "the raw model carries exactly two "
            + "intrinsicFunction bindings; got " + rawIntrinsic.size());
        for (IntrinsicKind kind : IntrinsicKind.values()) {
            RawBinding binding = rawIntrinsic.get(kind.name());
            check(binding != null, "the raw model carries the " + kind + " binding");
            if (binding == null) {
                continue;
            }
            check(kind.declaredSignature().canonicalSpecText().equals(binding.descriptor()),
                "the raw " + kind + " binding carries the pinned descriptor text; got "
                    + binding.descriptor());
        }

        // Direction 2: the unit text mapping (both codec directions).
        String text = ContractSnapshotCanonicalizer.serializeText(
            ContractSnapshotCanonicalizer.toJson(raw));
        RawUnit decoded = ContractSnapshotCanonicalizer.parseUnit(
            (CanonicalJson.Obj) ContractSnapshotCanonicalizer.parseValidationText(text));
        Map<String, RawBinding> decodedIntrinsic = new LinkedHashMap<>();
        for (RawBinding binding : decoded.bindings()) {
            if ("intrinsicFunction".equals(binding.shape())) {
                decodedIntrinsic.put(binding.intrinsicKind(), binding);
            }
        }
        check(decodedIntrinsic.equals(rawIntrinsic),
            "the decoded text carries byte-equal intrinsicFunction raw positions; got "
                + decodedIntrinsic);

        // Direction 3: the typed binding renderer (the op-payload direction).
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            if (!(entry.getValue() instanceof FunctionExecutionBinding.IntrinsicFunction
                    intrinsic)) {
                continue;
            }
            deal.semantic.ir.CanonicalJson.Value json =
                ContractSnapshotCanonicalizer.bindingJson(intrinsic);            String rendered = ContractSnapshotCanonicalizer.serializeText(json);
            check(rendered.contains("\"type\":\"intrinsicFunction\"")
                    && rendered.contains("\"intrinsicKind\":\"" + intrinsic.kind().name() + "\"")
                    && rendered.contains("\"descriptor\":\""
                        + intrinsic.kind().declaredSignature().canonicalSpecText() + "\""),
                "the typed binding renderer carries the shape tag, kind, and descriptor; got "
                    + rendered);
        }
    }

    // =========================================================================
    // 3. The closed gate admission: the produced unit passes with the seed
    //    BINDING_INIT as the key's producing position
    // =========================================================================

    private static void testClosedGatePositive() {
        System.out.println("-- closed gate: the produced unit passes with the seed init as "
            + "the producing position --");

        SemanticLowerer.ValidationCoreResult result = validUnit(
            "function main(): null { let a: int = 1; }", "the gate-admission slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        StructuredBodyTable table = result.lowering().table();

        check(BindingsProductionValidator.validate(unit, table).isEmpty(),
            "the produced unit passes REGISTRY_ONE_TO_ONE (the seed BINDING_INIT is the "
                + "IntrinsicFunction key's producing position)");
        // The walk's own pinned facts also pass (the alias/parameter arms are
        // part of the production chain the entry ran).
        check(BindingsProductionValidator.validate(unit, table,
                BindingsProductionValidator.PinnedWriteFacts.empty()).isEmpty(),
            "the produced unit passes the closed bindings gate");
        check(SemanticIrValidator.validate(unit, comparisonFacts()).isEmpty(),
            "the produced unit passes the closed 14 rules with the intrinsic shape admitted");
    }

    // =========================================================================
    // 4. The four negative seeds and the open-position negatives
    // =========================================================================

    private static final BlockId INIT_BLOCK = new BlockId(0);
    private static final RuntimeDescriptor INT = RuntimeDescriptor.Int.INSTANCE;
    private static final RuntimeDescriptor.Func SIG0 =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);

    private static int nextOp = 1;
    private static int nextVal = 1;
    private static int nextBinding = 1;

    private static OpId nextOpId() {
        return new OpId(MODULE, nextOp++);
    }

    private static ValueId nextValue() {
        return new ValueId(nextVal++);
    }

    private static BindingId nextBindingId() {
        return new BindingId(nextBinding++);
    }

    private static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
            OpResultType resultType, FailurePolicyId policy) {
        List<RuntimeDescriptor> operandTypes = List.of();
        List<ValueId> operands = List.of();
        ClosedSelector selector =
            payload instanceof KindPayload.SelectorCarrying carrying ? carrying.selector() : null;
        OperationContractSnapshot contract = new OperationContractSnapshot(
            OperationContractSnapshot.VERSION, kind, resultType, operandTypes, selector,
            payload, policy, List.of(), "placeholder");
        contract = new OperationContractSnapshot(OperationContractSnapshot.VERSION, kind,
            resultType, operandTypes, selector, payload, policy, List.of(),
            ContractSnapshotCanonicalizer.digest(contract));
        SourceOrigin origin = new SourceOrigin(SOURCE_ID, SourceSpan.synthetic(SOURCE_ID),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), null);
        return new SemanticOp(nextOpId(), kind, origin, result, resultType, operands,
            operandTypes, payload, policy, contract);
    }

    private static SemanticOp allocOp(BindingId binding, BlockId scope, long generation) {
        return op(SemanticOpKind.BINDING_ALLOC,
            new KindPayload.BindingAllocPayload(binding, scope, true,
                BindingCellKind.DIRECT, generation),
            null, null, FailurePolicyId.NO_DEAL_FAILURE);
    }

    private static SemanticOp initOp(BindingId binding, long generation, ValueId value) {
        return op(SemanticOpKind.BINDING_INIT,
            new KindPayload.BindingInitPayload(binding, generation, value),
            null, null, FailurePolicyId.NO_DEAL_FAILURE);
    }

    private static SemanticOp constIntOp(ValueId result) {
        return op(SemanticOpKind.CONST,
            new KindPayload.ConstPayload(new ScalarValue.Int(1)),
            result, INT, FailurePolicyId.NO_DEAL_FAILURE);
    }

    private static LoweredModuleUnit unit(
            Map<FunctionAllocationIdentity, FunctionExecutionBinding> registry,
            List<SemanticOp> ops) {
        return new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, MODULE, INTERFACE_HASH,
            LoweringContextHash.of(SemanticProfile.DEAL_V1_2_INT32, REGISTRY_HASH),
            Set.of(), Map.of(), Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), INIT_BLOCK), ExportPlan.empty(), registry, ops);
    }

    private static StructuredBodyTable tableOf(List<SemanticOp> ops) {
        Map<BlockId, List<OpId>> blockOps = new LinkedHashMap<>();
        Map<OpId, BlockId> inverse = new LinkedHashMap<>();
        List<OpId> ids = new ArrayList<>();
        for (SemanticOp op : ops) {
            ids.add(op.opId());
            inverse.put(op.opId(), INIT_BLOCK);
        }
        blockOps.put(INIT_BLOCK, ids);
        return new StructuredBodyTable(blockOps, inverse);
    }

    private static void assertRule(Optional<CompilerDiagnostic> failure, String rule,
                                   String what) {
        assertRule(failure, rule, "BINDINGS", what);
    }

    private static void assertRule(Optional<CompilerDiagnostic> failure, String rule,
                                   String capability, String what) {
        check(failure.isPresent(), what + " fails the closed gate");
        if (failure.isEmpty()) {
            return;
        }
        String message = failure.get().message();
        check("E6005".equals(failure.get().code()), what + " is rejected with E6005");
        check(failure.get().diagnosticCode() == DiagnosticCode.E6005,
            what + " carries the canonical E6005 code");
        String[] byRule = message.split("validatorRule ");
        check(byRule.length == 2 && byRule[1].startsWith(rule + ","),
            what + " is named as the validator rule " + rule + "; got \"" + message + "\"");
        check(message.contains("capability " + capability),
            what + " message carries capability " + capability);
    }

    private static void testNegativeSeeds() {
        System.out.println("-- the four negative seeds --");

        // (1) A seeded key with no seed BINDING_INIT.
        ValueId orphanKey = nextValue();
        List<SemanticOp> noInitOps = List.of(constIntOp(nextValue()));
        LoweredModuleUnit noInit = unit(
            Map.of(new FunctionAllocationIdentity(orphanKey.id()),
                new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                    IntrinsicKind.INT_CONVERT.declaredSignature())),
            noInitOps);
        assertRule(BindingsProductionValidator.validate(noInit, tableOf(noInitOps)),
            "REGISTRY_ONE_TO_ONE", "a seeded key with no seed BINDING_INIT");

        // (2) A seeded key with two seed BINDING_INITs (two incarnations, one
        //     shared producer-less operand).
        BindingId x = nextBindingId();
        BindingId y = nextBindingId();
        ValueId sharedSeed = nextValue();
        List<SemanticOp> twoInits = List.of(allocOp(x, INIT_BLOCK, 0), initOp(x, 0, sharedSeed),
            allocOp(y, INIT_BLOCK, 0), initOp(y, 0, sharedSeed));
        LoweredModuleUnit doubled = unit(
            Map.of(new FunctionAllocationIdentity(sharedSeed.id()),
                new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.NUMBER_CONVERT,
                    IntrinsicKind.NUMBER_CONVERT.declaredSignature())),
            twoInits);
        assertRule(BindingsProductionValidator.validate(doubled, tableOf(twoInits)),
            "REGISTRY_ONE_TO_ONE", "a seeded key with two seed BINDING_INITs");

        // (3) A producer-less init operand without a registration.
        BindingId z = nextBindingId();
        ValueId unregistered = nextValue();
        List<SemanticOp> unregisteredInits =
            List.of(allocOp(z, INIT_BLOCK, 0), initOp(z, 0, unregistered));
        LoweredModuleUnit orphanInit = unit(Map.of(), unregisteredInits);
        assertRule(BindingsProductionValidator.validate(orphanInit,
                tableOf(unregisteredInits)),
            "REGISTRY_ONE_TO_ONE", "a producer-less init operand without a registration");

        // (4) A mismatched (kind, descriptor) pair.
        BindingId w = nextBindingId();
        ValueId seed = nextValue();
        List<SemanticOp> mismatchedOps = List.of(allocOp(w, INIT_BLOCK, 0), initOp(w, 0, seed));
        LoweredModuleUnit mismatched = unit(
            Map.of(new FunctionAllocationIdentity(seed.id()),
                new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                    new RuntimeDescriptor.Func(List.of(RuntimeDescriptor.Int.INSTANCE),
                        RuntimeDescriptor.Int.INSTANCE))),
            mismatchedOps);
        assertRule(BindingsProductionValidator.validate(mismatched, tableOf(mismatchedOps)),
            "REGISTRY_ONE_TO_ONE", "a mismatched (kind, descriptor) pair");

        // The positive control: the same shapes with the correct registration
        // and exactly one seed init pass.
        BindingId v = nextBindingId();
        ValueId okSeed = nextValue();
        List<SemanticOp> okOps = List.of(allocOp(v, INIT_BLOCK, 0), initOp(v, 0, okSeed));
        LoweredModuleUnit admitted = unit(
            Map.of(new FunctionAllocationIdentity(okSeed.id()),
                new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.NUMBER_CONVERT,
                    IntrinsicKind.NUMBER_CONVERT.declaredSignature())),
            okOps);
        check(BindingsProductionValidator.validate(admitted, tableOf(okOps)).isEmpty(),
            "the same shape with one seed init and the pinned pair is admitted");
    }

    /**
     * The open IntrinsicKind position and the admitted nested callee shape
     * (ISSUE-0679 retargeted the landed pin: the nested static-callee shape
     * enumeration admits {@code intrinsicFunction}, and this incomplete fixture
     * now fails the later closed condition instead).
     */
    private static void testOpenPositionNegatives() {
        System.out.println("-- R-ENUM: the open intrinsic-kind position and the admitted "
            + "nested intrinsic callee shape --");

        SemanticLowerer.ValidationCoreResult result = validUnit(
            "function main(): null { let a: int = 1; }", "the open-position slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        String dump = SemanticIrDumper.dumpModuleText(unit);
        String mutated = dump.replaceFirst("\"intrinsicKind\":\"INT_CONVERT\"",
            "\"intrinsicKind\":\"INT_OPEN\"");
        check(!mutated.equals(dump), "the dump carries the INT_CONVERT kind position");
        Optional<CompilerDiagnostic> failure =
            SemanticIrValidator.validateText(mutated, comparisonFacts());
        assertRule(failure, "R-ENUM", "FOUNDATION_VALUES",
            "an open IntrinsicKind value in a closed position");

        // The nested static-callee shape enumeration admits the intrinsic
        // function value's shape (ISSUE-0679): the design's
        // CallCallee.Static(IntrinsicFunction) payload is the indirect
        // intrinsic call's arm, so R-ENUM no longer rejects the callee shape.
        // This incomplete fixture carries no recorded host cell family and no
        // registration for its function-typed result, so it fails a later
        // closed condition instead of the shape gate (the completed unit's
        // admission is the value-call battery's).
        FunctionExecutionBinding.IntrinsicFunction intrinsic =
            new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                IntrinsicKind.INT_CONVERT.declaredSignature());
        SemanticOp call = op(SemanticOpKind.CALL,
            new KindPayload.CallPayload(CallMode.INDIRECT,
                new KindPayload.CallCallee.Static(intrinsic), SIG0, List.of(), null, null,
                null, null),
            nextValue(), SIG0, FailurePolicyId.NO_DEAL_FAILURE);
        LoweredModuleUnit calleeUnit = unit(Map.of(), List.of(call));
        Optional<CompilerDiagnostic> calleeFailure =
            SemanticIrValidator.validate(calleeUnit, comparisonFacts());
        check(calleeFailure.isPresent(), "the incomplete intrinsic callee fixture fails "
            + "the closed gate");
        check(calleeFailure.map(d -> !d.message().contains("validatorRule R-ENUM,"))
                .orElse(true),
            "the intrinsic binding in a static CALLEE position is admitted by the nested "
                + "shape enumeration (no R-ENUM on the callee shape); got "
                + calleeFailure.map(CompilerDiagnostic::message).orElse("admission"));
        assertRule(calleeFailure, "R-BOUNDARY-TRIPLE", "FOUNDATION_VALUES",
            "the incomplete fixture (the intrinsic's registration without its recorded "
                + "host cell family)");

        // The admitted shape keeps the shape position's closed discipline: the
        // nested kind resolves in the closed IntrinsicKind set and both the
        // kind and the descriptor positions are present.
        String calleeText = SemanticIrValidator.toUnitText(calleeUnit);
        String nestedShape = "\"binding\":{\"descriptor\":\""
            + IntrinsicKind.INT_CONVERT.declaredSignature().canonicalSpecText()
            + "\",\"intrinsicKind\":\"INT_CONVERT\",\"type\":\"intrinsicFunction\"}"
            + ",\"type\":\"static\"";
        check(calleeText.contains(nestedShape),
            "the constructed fixture's text carries the nested intrinsic callee shape "
                + "position");
        if (calleeText.contains(nestedShape)) {
            assertRule(SemanticIrValidator.validateText(calleeText.replace(nestedShape,
                    nestedShape.replace("\"INT_CONVERT\"", "\"INT_OPEN\"")),
                    comparisonFacts()), "R-ENUM", "FOUNDATION_VALUES",
                "an open nested intrinsic callee kind");
            assertRule(SemanticIrValidator.validateText(calleeText.replace(nestedShape,
                    nestedShape.replace(",\"intrinsicKind\":\"INT_CONVERT\"", "")),
                    comparisonFacts()), "R-ENUM", "FOUNDATION_VALUES",
                "a nested intrinsic callee without its kind position");
            assertRule(SemanticIrValidator.validateText(calleeText.replace(nestedShape,
                    nestedShape.replace("\"descriptor\":\""
                        + IntrinsicKind.INT_CONVERT.declaredSignature().canonicalSpecText()
                        + "\",", "")),
                    comparisonFacts()), "R-ENUM", "FOUNDATION_VALUES",
                "a nested intrinsic callee without its descriptor position");
        }
    }

    // =========================================================================
    // 4b. The identity-preserving function-typed load of the seeded binding
    //     (ISSUE-0674 J1: the producer-less-test refinement)
    // =========================================================================

    /** One function-typed load of the named incarnation's cell. */
    private static SemanticOp loadOp(BindingId binding, long generation, ValueId result) {
        return op(SemanticOpKind.BINDING_LOAD,
            new KindPayload.BindingLoadPayload(binding, generation), result,
            IntrinsicKind.INT_CONVERT.declaredSignature(), FailurePolicyId.NO_DEAL_FAILURE);
    }

    /** One member/export read publishing the given identity (a non-load producer). */
    private static SemanticOp exportReadOp(ValueId identity) {
        return op(SemanticOpKind.EXPORT_READ,
            new KindPayload.ExportReadPayload(MODULE, "f",
                IntrinsicKind.INT_CONVERT.declaredSignature(), identity),
            identity, IntrinsicKind.INT_CONVERT.declaredSignature(),
            FailurePolicyId.NO_DEAL_FAILURE);
    }

    private static void testIdentityPreservingLoadAdmission() {
        System.out.println("-- the identity-preserving function-typed load of the seeded "
            + "binding (J1) --");

        // The load-shaped positive: a function-typed load naming the seed
        // BINDING_INIT's {binding, generation} whose result is that init's
        // operand identity is not a producing position, so the seeded key keeps
        // exactly one seed BINDING_INIT and the unit passes.
        BindingId seed = nextBindingId();
        ValueId seeded = nextValue();
        List<SemanticOp> seedOps = List.of(allocOp(seed, INIT_BLOCK, 0),
            initOp(seed, 0, seeded), loadOp(seed, 0, seeded));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> seededRegistry = Map.of(
            new FunctionAllocationIdentity(seeded.id()),
            new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.INT_CONVERT,
                IntrinsicKind.INT_CONVERT.declaredSignature()));
        LoweredModuleUnit loaded = unit(seededRegistry, seedOps);
        check(BindingsProductionValidator.validate(loaded, tableOf(seedOps)).isEmpty(),
            "the unit carrying the function-typed load of the seeded intrinsic binding "
                + "passes REGISTRY_ONE_TO_ONE (the load is not a producing position): "
                + BindingsProductionValidator.validate(loaded, tableOf(seedOps))
                    .map(CompilerDiagnostic::message).orElse("admission"));
        check(BindingsProductionValidator.validate(loaded, tableOf(seedOps),
                BindingsProductionValidator.PinnedWriteFacts.empty()).isEmpty(),
            "the load-carrying unit passes the closed bindings gate");

        // The load of another binding is not an identity-preserving load of the
        // seeded binding: the seeded identity is produced and the seed clause
        // fails closed.
        BindingId other = nextBindingId();
        ValueId otherValue = nextValue();
        List<SemanticOp> foreignOps = List.of(allocOp(seed, INIT_BLOCK, 0),
            initOp(seed, 0, seeded), constIntOp(otherValue),
            allocOp(other, INIT_BLOCK, 0), initOp(other, 0, otherValue),
            loadOp(other, 0, seeded));
        LoweredModuleUnit foreignLoad = unit(seededRegistry, foreignOps);
        Optional<CompilerDiagnostic> foreignFailure =
            BindingsProductionValidator.validate(foreignLoad, tableOf(foreignOps));
        assertRule(foreignFailure, "REGISTRY_ONE_TO_ONE",
            "a load naming another binding over the seeded identity");
        check(foreignFailure
                .map(d -> d.message().contains("is produced by 0 producing op(s), 0 host "
                    + "crossing(s), and 0 seed BINDING_INIT(s)")).orElse(false),
            "the foreign-binding load turns the seeded identity into a produced one (the "
                + "seed clause counts zero seed BINDING_INITs)");

        // The load of another generation of the seeded binding does not qualify
        // either.
        BindingId generationSeed = nextBindingId();
        ValueId generationSeeded = nextValue();
        ValueId laterValue = nextValue();
        List<SemanticOp> laterOps = List.of(allocOp(generationSeed, INIT_BLOCK, 0),
            initOp(generationSeed, 0, generationSeeded),
            constIntOp(laterValue), allocOp(generationSeed, INIT_BLOCK, 1),
            initOp(generationSeed, 1, laterValue),
            loadOp(generationSeed, 1, generationSeeded));
        Map<FunctionAllocationIdentity, FunctionExecutionBinding> laterRegistry = Map.of(
            new FunctionAllocationIdentity(generationSeeded.id()),
            new FunctionExecutionBinding.IntrinsicFunction(IntrinsicKind.NUMBER_CONVERT,
                IntrinsicKind.NUMBER_CONVERT.declaredSignature()));
        LoweredModuleUnit laterLoad = unit(laterRegistry, laterOps);
        Optional<CompilerDiagnostic> generationFailure =
            BindingsProductionValidator.validate(laterLoad, tableOf(laterOps));
        assertRule(generationFailure, "REGISTRY_ONE_TO_ONE",
            "a load naming another generation of the seeded binding");
        check(generationFailure
                .map(d -> d.message().contains("is produced by 0 producing op(s), 0 host "
                    + "crossing(s), and 0 seed BINDING_INIT(s)")).orElse(false),
            "the other-generation load turns the seeded identity into a produced one (the "
                + "seed clause counts zero seed BINDING_INITs)");

        // Every other op result carrying the seeded identity keeps the clause
        // rejecting: a member/export read is not an identity-preserving load.
        List<SemanticOp> readOps = List.of(allocOp(seed, INIT_BLOCK, 0),
            initOp(seed, 0, seeded), exportReadOp(seeded));
        LoweredModuleUnit readProduced = unit(seededRegistry, readOps);
        Optional<CompilerDiagnostic> readFailure =
            BindingsProductionValidator.validate(readProduced, tableOf(readOps));
        assertRule(readFailure, "REGISTRY_ONE_TO_ONE",
            "an EXPORT_READ carrying the seeded identity");
        check(readFailure
                .map(d -> d.message().contains("is produced by 1 producing op(s), 0 host "
                    + "crossing(s), and 0 seed BINDING_INIT(s)")).orElse(false),
            "the export-read production makes the seeded identity produced (the seed clause "
                + "counts zero seed BINDING_INITs)");

        // A producer-less init operand is admissible only under exactly one
        // IntrinsicFunction registration: the load-shaped unit without its
        // registration fails the converse clause.
        List<SemanticOp> noRegistrationOps = List.of(allocOp(seed, INIT_BLOCK, 0),
            initOp(seed, 0, seeded), loadOp(seed, 0, seeded));
        LoweredModuleUnit noRegistration = unit(Map.of(), noRegistrationOps);
        assertRule(BindingsProductionValidator.validate(noRegistration,
                tableOf(noRegistrationOps)), "REGISTRY_ONE_TO_ONE",
            "a producer-less init operand with no IntrinsicFunction registration");

        // The load itself is not a registration trigger: the seeded identity
        // keeps exactly one IntrinsicFunction registration (a
        // DynamicFunctionValue key for it stays rejected).
        LoweredModuleUnit dynamicOnSeed = unit(Map.of(
            new FunctionAllocationIdentity(seeded.id()),
            new FunctionExecutionBinding.DynamicFunctionValue(
                new OpId(MODULE, 4242),
                IntrinsicKind.INT_CONVERT.declaredSignature())),
            seedOps);
        assertRule(BindingsProductionValidator.validate(dynamicOnSeed, tableOf(seedOps)),
            "REGISTRY_ONE_TO_ONE",
            "a DynamicFunctionValue registration for the seeded identity");
    }

    // =========================================================================
    // 5. The registry entry point
    // =========================================================================

    private static void testRegistryEntryPoint() {
        System.out.println("-- FunctionBindingRegistry.registerIntrinsic --");

        FunctionBindingRegistry registry = new FunctionBindingRegistry();
        FunctionAllocationIdentity identity = new FunctionAllocationIdentity(4);
        registry.registerIntrinsic(identity, IntrinsicKind.INT_CONVERT,
            IntrinsicKind.INT_CONVERT.declaredSignature());
        check(registry.size() == 1, "one registration is recorded; got " + registry.size());
        FunctionExecutionBinding binding = registry.bindings().get(identity);
        check(binding instanceof FunctionExecutionBinding.IntrinsicFunction intrinsic
                && intrinsic.kind() == IntrinsicKind.INT_CONVERT
                && intrinsic.descriptor()
                    .equals(IntrinsicKind.INT_CONVERT.declaredSignature()),
            "the registration is the IntrinsicFunction binding with the given kind and "
                + "descriptor; got " + binding);
        try {
            registry.registerIntrinsic(identity, IntrinsicKind.INT_CONVERT,
                IntrinsicKind.INT_CONVERT.declaredSignature());
            fail("a duplicate-key registration must stay rejected at registration time");
        } catch (IllegalStateException expected) {
            passed++;
        }
        try {
            registry.bindings().put(new FunctionAllocationIdentity(9), binding);
            fail("the registration snapshot must be unmodifiable");
        } catch (UnsupportedOperationException expected) {
            passed++;
        }
    }

    // =========================================================================
    // 6. Combined behavior: source calls, an import alias, and adapters in one
    //    unit that carries the seed registrations
    // =========================================================================

    private static void testCombinedCorpus() {
        System.out.println("-- combined: source calls + import alias + adapters with the "
            + "seeds --");

        // (a) The validation-core entry (the entry that certifies the B9 rule
        //     set): the import alias and the adapters of one module, with the
        //     unit carrying the seed registrations.
        SemanticLowerer.ValidationCoreResult result = validUnit("""
            import * as m from "lib.math";
            function inner(x: int): null {}
            function main(): null {
              let a: int = 1;
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
              let n: (a: number, b: number) => int = int;
            }
            """, "the combined slice");
        if (result == null) {
            return;
        }
        LoweredModuleUnit unit = result.lowering().unit();
        List<SemanticOp> ops = unit.ops();

        check(intrinsicBindingCount(unit) == 2, "the combined unit carries both seed "
            + "registrations; got " + intrinsicBindingCount(unit));
        boolean adapter = false;
        boolean aliasAlloc = false;
        for (SemanticOp op : ops) {
            if (op.kind() == SemanticOpKind.FUNCTION_ADAPT) {
                adapter = true;
            }
            if (op.kind() == SemanticOpKind.BINDING_ALLOC
                    && op.payload() instanceof KindPayload.BindingAllocPayload alloc
                    && aliasFact(result.bindingFacts(), "m") != null
                    && alloc.binding().equals(aliasFact(result.bindingFacts(), "m"))) {
                aliasAlloc = true;
            }
        }
        check(adapter, "the combined unit carries a FUNCTION_ADAPT");
        check(aliasAlloc, "the combined unit carries the import-alias BINDING_ALLOC");
        check(BindingsProductionValidator.validate(unit, result.lowering().table()).isEmpty(),
            "the combined unit passes the closed bindings gate with the seeds, the import "
                + "alias, and the adapters");

        // (b) The E7 full-program entry (the existing entry that produces the
        //     E7-armed source-call arms with the reserved-identity takeover and
        //     the MODULE_IMPORT completion) composed with this slice's gate:
        //     the E7-armed unit carries the seed registrations and passes the
        //     bindings production validator.
        CheckedSlice slice = checkSlice("""
            import * as m from "lib.math";
            function inner(x: int): null {}
            function main(): null {
              let called: null = inner(1);
              let f: (x: int) => null = inner;
              let g: (a: int, b: int) => null = f;
            }
            """, "the E7-armed combined slice");
        if (slice == null) {
            return;
        }
        SemanticLowerer.FullProgramE7Result e7 = SemanticLowerer.lowerModuleFullProgramE7(
            new CheckedModuleInput(MODULE, SOURCE_ID, Path.of(SOURCE_ID), slice.program(),
                slice.checks(), importsOf(slice.program()), List.of(),
                CheckedModuleKind.IMPLEMENTATION),
            SemanticProfile.DEAL_V1_2_INT32, Map.of(), INTERFACE_HASH, REGISTRY_HASH,
            SemanticIdAllocator.over(List.of(MODULE)), Map.of(), Map.of(), Set.of());
        check(e7 != null && !e7.lowering().hasErrors() && e7.lowering().unit() != null,
            "the E7-armed combined slice lowers: "
                + (e7 == null ? "null" : e7.lowering().diagnostics()));
        if (e7 == null || e7.lowering().hasErrors() || e7.lowering().unit() == null) {
            return;
        }
        LoweredModuleUnit e7Unit = e7.lowering().unit();
        check(intrinsicBindingCount(e7Unit) == 2, "the E7-armed unit carries both seed "
            + "registrations; got " + intrinsicBindingCount(e7Unit));
        boolean call = false;
        boolean moduleImport = false;
        for (SemanticOp op : e7Unit.ops()) {
            if (op.kind() == SemanticOpKind.CALL) {
                call = true;
            }
            if (op.kind() == SemanticOpKind.MODULE_IMPORT) {
                moduleImport = true;
            }
        }
        check(call, "the E7-armed unit carries a source CALL");
        check(moduleImport, "the E7-armed unit carries the MODULE_IMPORT completion");
        check(BindingsProductionValidator.validate(e7Unit, e7.lowering().table(),
                BindingsProductionValidator.PinnedWriteFacts.empty()).isEmpty(),
            "the E7-armed unit (source calls, import alias, adapters, seeds) passes the "
                + "bindings production validator: "
                + BindingsProductionValidator.validate(e7Unit, e7.lowering().table(),
                    BindingsProductionValidator.PinnedWriteFacts.empty()));
    }

    private static int intrinsicBindingCount(LoweredModuleUnit unit) {
        int count = 0;
        for (FunctionExecutionBinding value : unit.functionBindings().values()) {
            if (value instanceof FunctionExecutionBinding.IntrinsicFunction) {
                count++;
            }
        }
        return count;
    }

    private static BindingId aliasFact(SemanticLowerer.BindingCoreFacts facts, String name) {
        SemanticLowerer.BindingCoreBinding binding = bindingFact(facts, name);
        return binding == null ? null : binding.binding();
    }

    // =========================================================================
    // Runner
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Intrinsic Seed Bindings / Closed Gate Admission Test "
            + "(ISSUE-0632) ===\n");

        testSeedRegistrationsTypedAndDump();
        testCodecRoundTrip();
        testClosedGatePositive();
        testNegativeSeeds();
        testIdentityPreservingLoadAdmission();
        testOpenPositionNegatives();
        testRegistryEntryPoint();
        testCombinedCorpus();

        System.out.println("\nIntrinsic seed bindings: " + passed + " passed, " + failed
            + " failed");
        if (failed > 0) {
            System.exit(1);
        }
    }
}
