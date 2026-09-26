package deal.semantic.ir;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * The raw unit of the validator's intermediate model (schema S1/S6): the
 * validator's pinned input over both surfaces. The typed surface produces
 * it through {@link #fromTyped(LoweredModuleUnit)} (enum names and payload
 * JSON extracted through T3's canonicalizer); the text surface produces it
 * through the single canonical JSON parser via
 * {@link ContractSnapshotCanonicalizer#parseUnit(CanonicalJson.Obj)}
 * with every closed enum position carried as a raw string. The closed
 * 14-condition rule engine consumes exactly this model on both surfaces.
 *
 * @param modulePath          the module identity path; non-null
 * @param semanticProfile     the raw semantic-profile name; non-null
 * @param interfaceHash       the interface index digest the unit was checked against; non-null
 * @param loweringContextHash the pinned lowering-context digest; non-null
 * @param requiredCapabilities the raw claimed capability names; non-null
 * @param coverage            the recorded construct-coverage rows; non-null
 * @param bindings            the function execution bindings keyed by
 *                            allocation identity; non-null
 * @param ops                 the produced operations in source order; non-null
 */
public record RawUnit(
    String modulePath,
    String semanticProfile,
    String interfaceHash,
    String loweringContextHash,
    List<String> requiredCapabilities,
    List<RawCoverage> coverage,
    List<RawBinding> bindings,
    List<RawOp> ops
) {

    public RawUnit {
        Objects.requireNonNull(modulePath, "modulePath must not be null");
        Objects.requireNonNull(semanticProfile, "semanticProfile must not be null");
        Objects.requireNonNull(interfaceHash, "interfaceHash must not be null");
        Objects.requireNonNull(loweringContextHash, "loweringContextHash must not be null");
        requiredCapabilities =
            List.copyOf(Objects.requireNonNull(requiredCapabilities, "requiredCapabilities must not be null"));
        coverage = List.copyOf(Objects.requireNonNull(coverage, "coverage must not be null"));
        bindings = List.copyOf(Objects.requireNonNull(bindings, "bindings must not be null"));
        ops = List.copyOf(Objects.requireNonNull(ops, "ops must not be null"));
    }

    /**
     * The typed-surface converter: maps a closed
     * {@link LoweredModuleUnit} onto the raw model — enum values render as
     * their names, descriptors as canonical spec texts, payloads through
     * {@link ContractSnapshotCanonicalizer#payloadJson}, and contracts
     * through {@link ContractSnapshotCanonicalizer#toJson}. The typed
     * enums are closed, so every raw name is a valid closed value here;
     * the invalid-value classes are injectable only through the text
     * surface.
     *
     * @param unit the typed unit; non-null
     * @return the raw unit
     */
    public static RawUnit fromTyped(LoweredModuleUnit unit) {
        List<String> capabilities = new ArrayList<>();
        for (SemanticCapability capability : unit.requiredCapabilities()) {
            capabilities.add(capability.name());
        }
        List<RawCoverage> coverage = new ArrayList<>();
        for (Map.Entry<ConstructKind, List<SemanticOpKind>> entry
                : unit.constructCoverage().entrySet()) {
            List<String> kinds = new ArrayList<>();
            for (SemanticOpKind kind : entry.getValue()) {
                kinds.add(kind.name());
            }
            coverage.add(new RawCoverage(entry.getKey().name(), kinds));
        }
        List<RawBinding> bindings = new ArrayList<>();
        for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                : unit.functionBindings().entrySet()) {
            bindings.add(bindingFromTyped(entry.getKey().id(), entry.getValue()));
        }
        List<RawOp> ops = new ArrayList<>();
        for (SemanticOp op : unit.ops()) {
            ops.add(opFromTyped(op));
        }
        return new RawUnit(unit.moduleId().path(), unit.semanticProfile().name(),
            unit.interfaceHash(), unit.loweringContextHash(), capabilities, coverage,
            bindings, ops);
    }

    private static RawBinding bindingFromTyped(long allocationId, FunctionExecutionBinding binding) {
        return switch (binding) {
            case FunctionExecutionBinding.LoweredBody ignored ->
                new RawBinding(allocationId, "loweredBody", null, null, null, null, null, null);
            case FunctionExecutionBinding.AdapterBinding adapter ->
                new RawBinding(allocationId, "adapter", null, null, null,
                    adapter.captureMode().name(), null,
                    adapter.targetSignature().canonicalSpecText());
            case FunctionExecutionBinding.HostFunction host ->
                new RawBinding(allocationId, "hostFunction", host.hostModuleId().path(),
                    host.exportName(), null, null, host.descriptor().canonicalSpecText(), null);
            case FunctionExecutionBinding.HostFunctionValue hostValue ->
                new RawBinding(allocationId, "hostFunctionValue", hostValue.hostModuleId().path(),
                    null, null, null, hostValue.descriptor().canonicalSpecText(), null,
                    hostValue.materializingBoundaryOpId());
            case FunctionExecutionBinding.ExternalFunction external ->
                new RawBinding(allocationId, "externalFunction", external.moduleId().path(),
                    external.exportName(), external.executionOwner().name(), null,
                    external.descriptor().canonicalSpecText(), null);
            case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                new RawBinding(allocationId, "intrinsicFunction", null, null, null, null,
                    intrinsic.descriptor().canonicalSpecText(), null, null,
                    intrinsic.kind().name());
            case FunctionExecutionBinding.DynamicFunctionValue dynamic ->
                new RawBinding(allocationId, "dynamicFunctionValue", null, null, null, null,
                    dynamic.descriptor().canonicalSpecText(), null,
                    dynamic.materializingOpId());
        };
    }

    private static RawOp opFromTyped(SemanticOp op) {
        CanonicalJson.Value payloadValue = ContractSnapshotCanonicalizer.payloadJson(op.payload());
        CanonicalJson.Obj payload = (CanonicalJson.Obj) payloadValue;
        OperationContractSnapshot contract = op.contract();
        String selector = contract.selector() == null
            ? null
            : ContractSnapshotCanonicalizer.selectorName(contract.selector());
        ValueId resultValue = null;
        AsyncTokenId resultToken = null;
        if (op.result() instanceof ValueId value) {
            resultValue = value;
        } else if (op.result() instanceof AsyncTokenId token) {
            resultToken = token;
        }
        String resultType = null;
        if (op.resultType() instanceof RuntimeDescriptor descriptor) {
            resultType = descriptor.canonicalSpecText();
        } else if (op.resultType() instanceof InternalResultType internal) {
            resultType = internal.name();
        }
        List<String> operandTypes = new ArrayList<>();
        for (RuntimeDescriptor descriptor : op.operandTypes()) {
            operandTypes.add(descriptor.canonicalSpecText());
        }
        return new RawOp(op.opId(), op.kind().name(), op.failurePolicy().name(),
            op.origin().parentOpId(), resultValue, resultToken, resultType,
            op.operands(), operandTypes, payload, selector, contract.canonicalDigest(),
            (CanonicalJson.Obj) ContractSnapshotCanonicalizer.toJson(contract));
    }
}
