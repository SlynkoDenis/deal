package deal.semantic.ir;

import java.util.Objects;

/**
 * The closed function execution bindings of {@code deal.semantic-ir/1}
 * (parent "Function execution bindings"; schema S2). Every
 * function-producing allocation registers exactly one binding in its
 * unit's {@code functionBindings}, keyed by
 * {@link FunctionAllocationIdentity}; {@code CALL(INDIRECT)},
 * {@code CALLBACK_INVOKE}, and {@code ASYNC_START} resolve the callee's
 * allocation identity to its binding at execution and never infer it from
 * the call-site type.
 *
 * <p>Closed shape — exactly the seven variants below; no other binding
 * shape exists:</p>
 *
 * <ul>
 *   <li>{@link LoweredBody} — a DEAL function body (closure, group
 *       function, or method).</li>
 *   <li>{@link AdapterBinding} — a {@code FUNCTION_ADAPT} adapter running
 *       the D15 invocation protocol.</li>
 *   <li>{@link HostFunction} — an imported host function value.</li>
 *   <li>{@link HostFunctionValue} — a host-materialized function value
 *       produced at a host crossing.</li>
 *   <li>{@link ExternalFunction} — an imported external function whose
 *       execution owner is {@code SHARED_BODY} or {@code RETAINED_ABI}.</li>
 *   <li>{@link IntrinsicFunction} — a producer-less conversion intrinsic
 *       ({@code int}/{@code number}) registered by the lowering's
 *       intrinsic seed.</li>
 *   <li>{@link DynamicFunctionValue} — a function-typed materialization
 *       whose execution class is resolved from the materialized carrier
 *       at execution (a typed binding load, a container/class/namespace
 *       read, a call result, or an awaited completion).</li>
 * </ul>
 */
public sealed interface FunctionExecutionBinding
    permits FunctionExecutionBinding.LoweredBody,
            FunctionExecutionBinding.AdapterBinding,
            FunctionExecutionBinding.HostFunction,
            FunctionExecutionBinding.HostFunctionValue,
            FunctionExecutionBinding.ExternalFunction,
            FunctionExecutionBinding.IntrinsicFunction,
            FunctionExecutionBinding.DynamicFunctionValue {

    /** A DEAL function body. */
    record LoweredBody(FunctionId functionId, BlockId blockId) implements FunctionExecutionBinding {

        public LoweredBody {
            Objects.requireNonNull(functionId, "functionId must not be null");
            Objects.requireNonNull(blockId, "blockId must not be null");
        }
    }

    /** A {@code FUNCTION_ADAPT} adapter running the D15 invocation protocol. */
    record AdapterBinding(
        OpId adaptOpId,
        CaptureMode captureMode,
        AdaptSourceRef sourceRef,
        RuntimeDescriptor.Func sourceSignature,
        RuntimeDescriptor.Func targetSignature
    ) implements FunctionExecutionBinding {

        public AdapterBinding {
            Objects.requireNonNull(adaptOpId, "adaptOpId must not be null");
            Objects.requireNonNull(captureMode, "captureMode must not be null");
            Objects.requireNonNull(sourceRef, "sourceRef must not be null");
            Objects.requireNonNull(sourceSignature, "sourceSignature must not be null");
            Objects.requireNonNull(targetSignature, "targetSignature must not be null");
        }
    }

    /** An imported host function value. */
    record HostFunction(ModuleId hostModuleId, String exportName, RuntimeDescriptor.Func descriptor)
        implements FunctionExecutionBinding {

        public HostFunction {
            Objects.requireNonNull(hostModuleId, "hostModuleId must not be null");
            Objects.requireNonNull(exportName, "exportName must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }

    /**
     * A host-materialized function value produced at a host crossing,
     * naming the materializing boundary op (correlation id).
     */
    record HostFunctionValue(ModuleId hostModuleId, OpId materializingBoundaryOpId, RuntimeDescriptor.Func descriptor)
        implements FunctionExecutionBinding {

        public HostFunctionValue {
            Objects.requireNonNull(hostModuleId, "hostModuleId must not be null");
            Objects.requireNonNull(materializingBoundaryOpId, "materializingBoundaryOpId must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }

    /** An imported external function across a shared/shadow module edge. */
    record ExternalFunction(
        ModuleId moduleId,
        String exportName,
        RuntimeDescriptor.Func descriptor,
        ExternalExecutionOwner executionOwner
    ) implements FunctionExecutionBinding {

        public ExternalFunction {
            Objects.requireNonNull(moduleId, "moduleId must not be null");
            Objects.requireNonNull(exportName, "exportName must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
            Objects.requireNonNull(executionOwner, "executionOwner must not be null");
        }
    }

    /**
     * A producer-less conversion intrinsic ({@code int}/{@code number})
     * materialized as a first-class function value: the closed intrinsic
     * kind and the intrinsic's declared signature. The registration is
     * keyed by the seeded function-value identity (no closed op produces
     * it); the seeded identity's single {@code BINDING_INIT} is the
     * key's producing position, and the closed gate admits the pair
     * exactly when the descriptor is the kind's pinned declared
     * signature ({@link IntrinsicKind#declaredSignature()}).
     */
    record IntrinsicFunction(IntrinsicKind kind, RuntimeDescriptor.Func descriptor)
        implements FunctionExecutionBinding {

        public IntrinsicFunction {
            Objects.requireNonNull(kind, "kind must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }

    /**
     * A function-typed materialization whose execution class is resolved
     * from the materialized carrier at execution: the op that produces
     * the value identity and the value's checked function descriptor.
     * No execution class, owning module, or export is recorded, because
     * none is statically known — the class is the runtime value's own
     * producing registration at execution. The record is therefore never
     * a resolution input of
     * {@link DynamicReturnBoundaryProtocol#kindOf(FunctionExecutionBinding)}
     * (it fails closed on this shape); a call or await whose callee
     * resolves to it takes the closed dynamic arm.
     */
    record DynamicFunctionValue(OpId materializingOpId, RuntimeDescriptor.Func descriptor)
        implements FunctionExecutionBinding {

        public DynamicFunctionValue {
            Objects.requireNonNull(materializingOpId, "materializingOpId must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }
}
