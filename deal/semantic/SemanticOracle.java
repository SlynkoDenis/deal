package deal.semantic;

import deal.diagnostics.DiagnosticCode;
import deal.semantic.ir.ActualKind;
import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.DynamicResolutionKind;
import deal.semantic.ir.DynamicReturnBoundaryProtocol;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryContext;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryExecutor;
import deal.semantic.ir.BoundaryFailure;
import deal.semantic.ir.BoundaryOutcome;
import deal.semantic.ir.BoundaryValueView;
import deal.semantic.ir.ChainOperandCompletion;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClassOpsExecutor;
import deal.semantic.ir.ComparisonExecutor;
import deal.semantic.ir.ComparisonOperandView;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.NormalizedSlot;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ReturnBoundarySelection;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticArray;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticTable;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.UnicodeScalars;
import deal.semantic.ir.ValueId;

import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The semantic oracle of {@code deal.semantic-ir/1} — an independent
 * interpreter over a validated {@link LoweredModuleUnit} plus its
 * {@link StructuredBodyTable} (semantic-lowering-differential-conformance
 * D5; the oracle carrier of the decomposition-tail integration
 * verification, ISSUE-0410). It invokes no target backend, no generated
 * artifact, no Java execution of emitted code, and no LuaJIT: execution is
 * realized directly from the validated IR.
 *
 * <p><b>Execution shape (the decomposition-tail carrier contract).</b>
 * The oracle executes the entry module's module-init block in list order
 * (the unit's {@code ModuleInitPlan} block, whose ops include the
 * produced entry delegation — the lowerer's module-init-level
 * {@code CALL(DIRECT main)} followed by its {@code DISCARD}); the run's
 * result atom is the value the trailing {@code DISCARD} discarded (the
 * entry call's committed value). Every executed op emits exactly one
 * START and one terminal (SUCCESS/FAILURE) {@link
 * SemanticRuntimeModel.TraceEvent} carrying the op's contract digest and
 * the structural {@code parentOpId} of its validated origin; children
 * (boundary ops of calls, chains, and reads) execute with their own
 * events. Completed operands' atoms are the START inputs; the produced
 * value atom is the SUCCESS output; a DEAL failure publishes the exact
 * error snapshot (code, canonical message, origin, attained
 * expected/actual, active frames innermost-first, nested cause).
 * {@code STDLIB_CALL} executes through {@link SharedStdlibSemantics} —
 * the single stdlib algorithm executor — with the pinned precedence:
 * {@code STDLIB_PARAMETER} boundaries in one-based order, then the
 * algorithm (a failure resolves the primitive's registry-row projection
 * with the row's pinned origin and the active frames), then the single
 * {@code STDLIB_RETURN} boundary run by the call op. The
 * {@code TIME_NOW_MILLIS} operation reads the oracle's injected
 * deterministic clock reading (K7 item 4), never the host clock.
 * Console stdlib calls record one ordered
 * {@link SemanticRuntimeModel.EffectEvent}
 * per terminal. A DEAL failure escaping the module-init block is the
 * run's {@link SemanticRuntimeModel.Terminal.DealFailure}; otherwise the
 * run succeeds with the entry result atom.</p>
 *
 * <p><b>Runtime conventions pinned here (consumed identically by the
 * shared emitters).</b></p>
 * <ul>
 *   <li>Bindings: one runtime cell per {@code (BindingId, generation)}
 *       incarnation; {@code BINDING_ALLOC} creates the cell,
 *       {@code BINDING_INIT}/{@code BINDING_STORE} commit into it,
 *       {@code BINDING_LOAD} reads it (generation-checked). Closures
 *       capture the cells current at {@code CLOSURE_NEW} execution
 *       ({@code captures} are binding identities; loads inside the body
 *       carry their incarnation generations). A {@code FOR_EACH}
 *       iteration replaces the iteration binding's cell with a fresh one
 *       per iteration, so closures created in the body observe
 *       per-iteration values.</li>
 *   <li>Parameters: a callee body block's leading {@code BINDING_ALLOC}
 *       ops in list order are its parameter cells (the lowerer's
 *       body-entry parameter ALLOCs); a {@code CALL} binds the
 *       boundary-checked argument values to those cells before the
 *       remaining body ops execute.</li>
 *   <li>The single return boundary: {@code RETURN} executes the
 *       {@code FUNCTION_RETURN} boundary named by its payload (its
 *       origin's parent), publishes the checked value as the enclosing
 *       call's return value, and transfers. The CALL terminal records the
 *       value without re-checking.</li>
 *   <li>Transfers: {@code RETURN}/{@code BREAK}/{@code CONTINUE} succeed
 *       and then signal; the signal unwinds to the matching structure
 *       ({@code CALL} invocation, {@code LOOP}/{@code FOR_EACH} with the
 *       recorded target op) through enclosing {@code TRY_CATCH}es without
 *       being caught.</li>
 *   <li>Error values: {@code THROW} consumes an {@code Error} value
 *       ({@code code,message}); {@code TRY_CATCH} reifies a caught DEAL
 *       failure as an {@code Error} value bound to the catch binding; a
 *       catch failure carries its own origin with {@code cause} = the
 *       original snapshot. Only DEAL failures (E8) are catchable.</li>
 * </ul>
 *
 * <p><b>Purity of consumers.</b> The oracle, the shared LuaJIT emitter
 * artifact, and the shared JVM emitter artifact execute the identical
 * validated unit; the differential harness validates every event against
 * the exact IR op and compares the three reports event-for-event —
 * duplicated evaluations, wrong selectors, missing boundaries, and moved
 * children fail even when printed output coincides.</p>
 */
public final class SemanticOracle {

    private SemanticOracle() {
    }

    /** The module-level entry convention: {@code main} is the entry function. */
    public static final String ENTRY_FUNCTION = "main";

    /**
     * Executes the entry module of the validated project: the module-init
     * block in list order (which ends with the produced entry delegation
     * CALL + DISCARD), recording the exact semantic trace, the ordered
     * effects, and the terminal.
     *
     * @param unit  the validated lowered module unit; non-null
     * @param table the unit's produced block-membership table; non-null
     * @return the complete consumer run report
     */
    public static SemanticRuntimeModel.ConsumerRun execute(LoweredModuleUnit unit,
                                                           StructuredBodyTable table) {
        return execute(unit, table, null);
    }

    /**
     * Executes the entry module with the given deterministic host
     * responder (the E7 host seam): {@code CALL(HOST)}/host-source
     * adapter calls and async host operations resolve through the
     * responder — never through ambient host state. A host call without
     * a responder is a producer defect, never a silent projection.
     */
    public static SemanticRuntimeModel.ConsumerRun execute(LoweredModuleUnit unit,
                                                           StructuredBodyTable table,
                                                           HostResponder responder) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Execution state = new Execution(unit, table, responder);
        state.stateStack.push(state.units.get(unit.moduleId()));
        try {
            state.runModuleInit(unit);
        } catch (DealFailure failure) {
            return state.report(new SemanticRuntimeModel.Terminal.DealFailure(
                state.snapshot(failure)));
        } finally {
            state.stateStack.pop();
        }
        String resultAtom = state.entryResultAtom != null
            ? state.entryResultAtom : "null";
        return state.report(new SemanticRuntimeModel.Terminal.Success(resultAtom));
    }

    /**
     * Executes the entry module of a validated executable project with
     * the complete implementation closure: {@code CALL(EXTERNAL)}/
     * {@code ASYNC_START(EXTERNAL)} execute the callee unit's
     * {@code EXTERNAL_ENTRY} (sync: the callee {@code RETURN} runs the
     * single {@code EXTERNAL_RETURN} boundary and the value crosses the
     * ABI unchanged; async: the callee entry creates the canonical token
     * and the body task, the caller's alias token links through the
     * {@code ExternalAsyncLink}, and the caller's single
     * {@code ASYNC_COMPLETION} boundary validates the crossed value at
     * {@code AWAIT}). The entry module's run report is returned.
     */
    public static SemanticRuntimeModel.ConsumerRun execute(ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables, HostResponder responder) {
        return execute(project, tables, Map.of(), responder);
    }

    /**
     * Executes the entry module of a validated executable project with
     * the complete implementation closure plus the class-construction
     * production records (K-D2: one {@link ClassFactoryRegistry} per
     * module — the owner-side {@code CLASS_FACTORY} bindings a caller's
     * {@code CLASS_NEW(SHARED_FACTORY)} resolves through):
     * {@code CALL(EXTERNAL)}/{@code ASYNC_START(EXTERNAL)} execute the
     * callee unit's {@code EXTERNAL_ENTRY} (sync: the callee
     * {@code RETURN} runs the single {@code EXTERNAL_RETURN} boundary
     * and the value crosses the ABI unchanged; async: the callee entry
     * creates the canonical token and the body task, the caller's alias
     * token links through the {@code ExternalAsyncLink}, and the
     * caller's single {@code ASYNC_COMPLETION} boundary validates the
     * crossed value at {@code AWAIT}), and a
     * {@code CLASS_NEW(SHARED_FACTORY)} transfers default application
     * to the owner unit's registered {@code CLASS_FACTORY} op — the
     * factory's events parent to the triggering caller op
     * (cross-unit), its detached {@code CLASS_DEFAULT} children
     * evaluate in the declaring module's scope, and the caller's
     * {@code CLASS_DEFAULT_FIELD} boundaries read the named field of
     * the transferred instance. The entry module's run report is
     * returned.
     */
    public static SemanticRuntimeModel.ConsumerRun execute(ExecutableLoweredProject project,
            Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, HostResponder responder) {
        return executeClosure(project, tables, registries, responder, false);
    }

    /**
     * Executes the complete closure's module-init walks in dependency
     * (project insertion) order — the CLASSES cross-module surface: the
     * owner's module-level bindings initialize before any caller
     * construction evaluates its defaults, and the entry module's walk
     * runs last, exactly like the shared emitters' combined artifacts.
     * The entry module's run report is returned.
     */
    public static SemanticRuntimeModel.ConsumerRun executeProjectInits(
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, HostResponder responder) {
        return executeClosure(project, tables, registries, responder, true);
    }

    /** The shared closure executor (all-init or entry-only walks). */
    private static SemanticRuntimeModel.ConsumerRun executeClosure(
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            Map<ModuleId, ClassFactoryRegistry> registries, HostResponder responder,
            boolean allInits) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(registries, "registries must not be null");
        LoweredModuleUnit unit = project.modules().get(project.entryModule());
        if (unit == null) {
            throw new IllegalArgumentException("the entry module is not in the closure");
        }
        Execution state = new Execution(project, tables, registries, responder);
        try {
            for (Map.Entry<ModuleId, LoweredModuleUnit> moduleEntry
                    : project.modules().entrySet()) {
                if (!allInits && !moduleEntry.getKey().equals(project.entryModule())) {
                    continue;
                }
                state.runInit(moduleEntry.getKey(), moduleEntry.getValue());
            }
        } catch (DealFailure failure) {
            return state.report(new SemanticRuntimeModel.Terminal.DealFailure(
                state.snapshot(failure)));
        }
        String resultAtom = state.entryResultAtom != null
            ? state.entryResultAtom : "null";
        return state.report(new SemanticRuntimeModel.Terminal.Success(resultAtom));
    }

    /**
     * Host-driven callback invocation (the E7 callback surface): the
     * unit's {@code CALLBACK_INVOKE} record for the bound function value
     * executes top-level — the {@code HOST_TO_DEAL} parameter boundaries
     * in one-based order, the resolved execution binding, and the single
     * {@code DEAL_TO_HOST} return boundary (by the executed body's
     * {@code RETURN} for bodies and DEAL-body-source adapters, by the
     * callback op for host/external functions and host/external-source
     * adapters). Sync functions only.
     */
    public static SemanticRuntimeModel.ConsumerRun invokeCallback(LoweredModuleUnit unit,
            StructuredBodyTable table, ValueId functionValue, List<Value> args) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(functionValue, "functionValue must not be null");
        Objects.requireNonNull(args, "args must not be null");
        Execution state = new Execution(unit, table, null);
        SemanticOp callback = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.CALLBACK_INVOKE
                    && ((KindPayload.CallbackInvokePayload) op.payload()).function()
                        .equals(functionValue)) {
                callback = op;
                break;
            }
        }
        if (callback == null) {
            throw new IllegalArgumentException("the unit records no CALLBACK_INVOKE for "
                + functionValue + " (the callback surface is the lowerer's recorded "
                + "invocation, never an invented one)");
        }
        try {
            Value returned = state.executeCallback(callback, args);
            return state.report(new SemanticRuntimeModel.Terminal.Success(
                state.atomOf(returned)));
        } catch (DealFailure failure) {
            return state.report(new SemanticRuntimeModel.Terminal.DealFailure(
                state.snapshot(failure)));
        }
    }

    /**
     * Async-export invocation (the E7 cross-module async drive): the
     * callee module's async {@code EXTERNAL_ENTRY} creates its canonical
     * token and body task (the entry op id is the canonical token
     * identity), the deterministic FIFO drain runs the task exactly once
     * (the body's {@code RETURN} runs the single {@code FUNCTION_RETURN}
     * boundary), and the completed value/error is the run terminal —
     * caller-side {@code ASYNC_COMPLETION} boundaries run at the
     * caller's {@code AWAIT} sites inside the task itself.
     */
    public static SemanticRuntimeModel.ConsumerRun invokeAsyncEntry(
            ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
            HostResponder responder, ModuleId module, String exportName, List<Value> args) {
        Objects.requireNonNull(project, "project must not be null");
        Objects.requireNonNull(tables, "tables must not be null");
        Objects.requireNonNull(module, "module must not be null");
        Objects.requireNonNull(exportName, "exportName must not be null");
        Objects.requireNonNull(args, "args must not be null");
        LoweredModuleUnit unit = project.modules().get(module);
        if (unit == null) {
            throw new IllegalArgumentException("module " + module + " is not in the closure");
        }
        SemanticOp entry = null;
        for (SemanticOp op : unit.ops()) {
            if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY
                    && ((KindPayload.ExternalEntryPayload) op.payload()).exportName()
                        .equals(exportName)) {
                entry = op;
                break;
            }
        }
        if (entry == null) {
            throw new IllegalArgumentException("module " + module
                + " records no EXTERNAL_ENTRY for export '" + exportName + "'");
        }
        Execution state = new Execution(project, tables, responder);
        try {
            // Dependency initialization first: the module-init block
            // (bindings, imports, the inert entry delegation) runs once
            // before the async entry task executes.
            try {
                state.runModuleInit(unit);
            } catch (ReturnSignal | LoopSignal signal) {
                // The module-init block never transfers.
            }
            state.executeAsyncEntry(entry, null, List.copyOf(args), entry.opId().id());
            state.drainReadyTasks();
            Execution.Task task = state.tasks.get(entry.opId().id());
            if (task == null || !task.completed) {
                throw new IllegalStateException("the async entry task did not complete "
                    + "(producer defect)");
            }
            if (task.failure != null) {
                throw task.failure;
            }
            Value value = task.value == null ? Value.NullValue.INSTANCE : task.value;
            return state.report(new SemanticRuntimeModel.Terminal.Success(
                state.atomOf(value)));
        } catch (DealFailure failure) {
            return state.report(new SemanticRuntimeModel.Terminal.DealFailure(
                state.snapshot(failure)));
        }
    }

    /**
     * The deterministic host seam of the E7 call machine: a closed
     * responder supplies every host terminal — sync returns/throws,
     * async starts (an operation label, or a bad handle), and async
     * completions. The oracle records one ordered
     * {@code HOST_CALL}/{@code HOST_RETURN}/{@code HOST_THROW}/
     * {@code ASYNC_START_OP}/{@code ASYNC_COMPLETE_*} effect per
     * terminal, and a thrown host error crosses as a DEAL failure with
     * the host's code/message at the call origin.
     */
    public interface HostResponder {

        /** One sync host terminal: the returned value or the thrown host error. */
        sealed interface SyncOutcome permits SyncOutcome.Returned, SyncOutcome.Thrown {

            /** The host returned a value. */
            record Returned(Value value) implements SyncOutcome {
            }

            /** The host threw an error (code/message preserved). */
            record Thrown(String code, String message) implements SyncOutcome {
            }
        }

        /**
         * One sync host call terminal.
         *
         * @param module     the owning host module; non-null
         * @param export     the host export name; non-null
         * @param descriptor the declared function descriptor; non-null
         * @param args       the boundary-checked argument values; non-null
         * @return the terminal
         */
        default SyncOutcome call(ModuleId module, String export,
                                 RuntimeDescriptor.Func descriptor, List<Value> args) {
            throw new IllegalStateException("the responder scripts no sync host call for "
                + module + "." + export + " (the E7 host seam fails closed)");
        }

        /**
         * One async host start: returns the operation label the returned
         * handle binds to, or {@code null} for a bad handle (the
         * {@code ASYNC_OPERATION_HANDLE} terminal check fails).
         *
         * @param module         the owning host module; non-null
         * @param export         the host export name; non-null
         * @param descriptor     the declared async function descriptor; non-null
         * @param args           the boundary-checked argument values; non-null
         * @param operationLabel the deterministic operation label the
         *                       canonical token binds one-to-one to; non-null
         * @return the bound label, or {@code null} for a bad handle
         */
        default String startAsync(ModuleId module, String export,
                                  RuntimeDescriptor.Func descriptor, List<Value> args,
                                  String operationLabel) {
            return operationLabel;
        }

        /**
         * One async host completion: the completion value or the thrown
         * host error of the operation label.
         *
         * @param operationLabel the operation label; non-null
         * @return the completion terminal
         */
        default SyncOutcome completeAsync(String operationLabel) {
            return new SyncOutcome.Returned(Value.NullValue.INSTANCE);
        }
    }

    /**
     * The closed module-initialization lifecycle of the {@code MODULE_INIT}
     * op execution (E8): {@code INITIALIZING} during the payload walk,
     * {@code INITIALIZED} after a completed walk, {@code FAILED} after a
     * failing walk (no export publication). An unrecorded module is
     * {@code UNINITIALIZED}.
     */
    private enum ModuleInitLifecycle {
        INITIALIZING, INITIALIZED, FAILED
    }

    // =========================================================================
    // Runtime values
    // =========================================================================

    /** The oracle's closed runtime-value model. */
    public sealed interface Value
        permits Value.NullValue, Value.MissingValue, Value.BoolValue, Value.IntValue,
                Value.NumValue, Value.StrValue, Value.TableValue, Value.ArrayValue,
                Value.FuncValue, Value.AdapterValue, Value.IntrinsicValue, Value.ErrorValue,
                Value.SlotValue, Value.ClassValue, Value.StdlibCallableValue {

        enum NullValue implements Value { INSTANCE }

        enum MissingValue implements Value { INSTANCE }

        record BoolValue(boolean value) implements Value {
        }

        record IntValue(long value) implements Value {
        }

        record NumValue(double value) implements Value {
        }

        record StrValue(String value) implements Value {
        }

        /** An insertion-ordered table over string keys. */
        record TableValue(LinkedHashMap<String, Value> entries) implements Value {
        }

        /** A dense array; deleted slots hold {@link MissingValue}. */
        record ArrayValue(List<Value> elements, RuntimeDescriptor elementDescriptor)
            implements Value {
        }

        /** A closure allocation: the lowered body plus its captured cells. */
        record FuncValue(FunctionId function, RuntimeDescriptor.Func signature,
                         Map<BindingId, Cell> captures) implements Value {
        }

        /** An intrinsic function value (int()/number() as first-class values). */
        record IntrinsicValue(String name) implements Value {
        }

        /**
         * The in-target cataloged stdlib callable (M3/M4): one memoized
         * value per catalog row per module per run — the read of a
         * cataloged STDLIB export publishes this value, carrying the row tag
         * and the row's declared signature (the read's checked descriptor),
         * so a function-typed boundary sees the row's signature, never the
         * reading site's. The value is keyed once in
         * {@code bindingsByValue} at its creation (the read arm's
         * registration) and a read never re-keys it.
         */
        record StdlibCallableValue(StdlibFunctionId function,
                                   RuntimeDescriptor.Func descriptor) implements Value {

            public StdlibCallableValue {
                Objects.requireNonNull(function, "function must not be null");
                Objects.requireNonNull(descriptor, "descriptor must not be null");
            }
        }

        /** A {@code FUNCTION_ADAPT} adapter value (target signature). */
        record AdapterValue(RuntimeDescriptor.Func signature) implements Value {
        }

        /**
         * The caught/reified DEAL {@code Error} value — the builtin
         * {@code Error} class's runtime carrier {@code {code, message}}
         * (ISSUE-0619; {@code semantic-ir-construct-coverage-cutover}
         * K13). The value is mutable with reference identity: a class-field
         * write commits in place, so every alias of the instance observes
         * the written field exactly like the target carriers. Both fields
         * are always present (the declared layout is two required-present
         * strings; an omitted field carries the compiler constant empty
         * string), and the value converts to and from the closed executor
         * class view {@code Class(@/Error, [Present(code),
         * Present(message)])} — never to a generic class value.
         */
        final class ErrorValue implements Value {

            private String code;
            private String message;

            ErrorValue(String code, String message) {
                Objects.requireNonNull(code, "code must not be null");
                Objects.requireNonNull(message, "message must not be null");
                this.code = code;
                this.message = message;
            }

            /** The error code field. */
            String code() {
                return code;
            }

            /** The error message field. */
            String message() {
                return message;
            }

            /** Commits one checked field write in place (K13's field surface). */
            void writeField(String field, String value) {
                Objects.requireNonNull(value, "value must not be null");
                switch (field) {
                    case "code" -> this.code = value;
                    case "message" -> this.message = value;
                    default -> throw new IllegalStateException("the builtin Error"
                        + " carrier has no field '" + field + "' (producer defect)");
                }
            }
        }

        /** The normalize-computed slot (internal; never a language value). */
        record SlotValue(NormalizedSlot slot) implements Value {
        }

        /**
         * One class-field state of a {@link ClassValue} (the CLASSES
         * family's three-presence-state discipline, K-D6):
         * {@code Present(Value) | Missing} — present null (the explicit
         * {@link NullValue} variant) stays {@code Present} and is
         * distinguishable from {@code Missing}.
         */
        sealed interface ClassFieldState
            permits ClassFieldState.Present, ClassFieldState.Missing {

            /** The field is present; {@code value} is its value (never MissingValue). */
            record Present(Value value) implements ClassFieldState {

                public Present {
                    Objects.requireNonNull(value, "value must not be null");
                    if (value instanceof Value.MissingValue) {
                        throw new IllegalStateException("a present class field never "
                            + "carries the internal Missing view — absence is the "
                            + "Missing field state (producer defect)");
                    }
                }
            }

            /** The field is absent (the schema's internal missing). */
            enum Missing implements ClassFieldState {
                INSTANCE
            }
        }

        /**
         * A class instance: the canonical {@link ClassId} tag plus its
         * fields in declaration order as {@link ClassFieldState}
         * {@code Present | Missing} — present null stays present null
         * and is never conflated with a missing field (E5's
         * presence-preserving storage discipline). The declaration-order
         * state list is the instance's live storage: a field commit
         * ({@code FIELD_WRITE}/{@code FIELD_DELETE}) replaces one state in
         * place, so every reference to the instance observes the commit
         * (the target emitters mutate their instance carrier exactly the
         * same way).
         */
        record ClassValue(ClassId classId, List<ClassFieldState> fields)
            implements Value {

            public ClassValue {
                Objects.requireNonNull(classId, "classId must not be null");
                fields = new ArrayList<>(Objects.requireNonNull(fields,
                    "fields must not be null"));
            }

            /** Replaces one declaration-order field state in place (the commit op). */
            void replaceField(int index, ClassFieldState state) {
                fields.set(index, state);
            }
        }
    }

    /** One binding cell incarnation: binding, generation, and current value. */
    static final class Cell {
        final BindingId binding;
        final long generation;
        Value value;
        boolean initialized;

        Cell(BindingId binding, long generation) {
            this.binding = binding;
            this.generation = generation;
        }
    }

    /** A DEAL failure with its exact projection facts. */
    public static final class DealFailure extends RuntimeException {
        final String code;
        final String message;
        final SourceOrigin origin;
        final String expected;
        final String actual;
        final DealFailure cause;
        final List<FunctionId> frames;

        DealFailure(String code, String message, SourceOrigin origin,
                    String expected, String actual, DealFailure cause,
                    List<FunctionId> frames) {
            super(message, cause);
            this.code = code;
            this.message = message;
            this.origin = origin;
            this.expected = expected;
            this.actual = actual;
            this.cause = cause;
            this.frames = List.copyOf(frames);
        }

        static DealFailure of(BoundaryFailure failure, SourceOrigin origin,
                              List<FunctionId> frames) {
            return new DealFailure(failure.code().code(), failure.message(), origin,
                failure.expected(), failure.actual(), null, frames);
        }
    }

    /** A RETURN transfer: the checked value returns to the enclosing invocation. */
    static final class ReturnSignal extends RuntimeException {
        final Value value;

        ReturnSignal(Value value) {
            super(null, null, false, false);
            this.value = value;
        }
    }

    /** A BREAK/CONTINUE transfer naming the recorded loop target. */
    static final class LoopSignal extends RuntimeException {
        final OpId target;
        final boolean isContinue;

        LoopSignal(OpId target, boolean isContinue) {
            super(null, null, false, false);
            this.target = target;
            this.isContinue = isContinue;
        }
    }

    // =========================================================================
    // Execution state
    // =========================================================================

    private static final class Execution {
        final LoweredModuleUnit unit;
        final StructuredBodyTable table;
        /** The deterministic host responder (the E7 host seam); null outside host drives. */
        final HostResponder responder;
        /**
         * The class-construction production records by module (K-D2):
         * the owner-side {@code ClassFactoryRegistry} bindings a
         * caller's {@code CLASS_NEW(SHARED_FACTORY)} resolves through.
         */
        final Map<ModuleId, ClassFactoryRegistry> registries;
        /** The complete implementation closure (entry module included). */
        final Map<ModuleId, UnitState> units = new LinkedHashMap<>();
        /** The entry module's unit state. */
        final UnitState entry;
        /** The entry module's op index (single-unit aliases). */
        final Map<OpId, SemanticOp> opsById = new HashMap<>();
        /** One async task/operation state per canonical token identity. */
        final Map<Long, Task> tasks = new LinkedHashMap<>();
        /** The deterministic FIFO queue of pending DEAL body tasks. */
        final ArrayDeque<Long> readyQueue = new ArrayDeque<>();
        /** The canonical-token → host operation-label bindings. */
        final Map<Long, String> hostOperations = new LinkedHashMap<>();
        /**
         * The execution-bound external async token linkage of a
         * dynamically resolved ASYNC_START (ISSUE-0531): caller token
         * → callee EXTERNAL_ENTRY canonical token, bound when the
         * runtime resolves the callee to an async external.
         */
        final Map<Long, Long> dynamicReferents = new LinkedHashMap<>();
        /** The heap function value → resolved execution binding index. */
        final IdentityHashMap<Value, FunctionExecutionBinding> bindingsByValue =
            new IdentityHashMap<>();
        /**
         * The per-run published export surfaces (M3): one recorded
         * published value per {@code (module, name)} of the run, written
         * exactly once by the owning module's {@code EXPORT_PUBLISH} — the
         * oracle's mirror of the artifacts' program-scoped export-surface
         * registry. A HOST/FFI module's surface is its loaded module table
         * (the entry the host-load surface and the FFI child's
         * {@code load_ffi} surface record under the module identity), of
         * which a read resolves the named entry. An absent surface or entry
         * is the absent-slot projection ({@link Value.MissingValue}); the
         * registry is never written by a read.
         */
        final Map<ModuleId, Map<String, Value>> exportSurfaces =
            new LinkedHashMap<>();
        /**
         * The per-run cataloged-callable registry (M3/M4): one memoized
         * {@link Value.StdlibCallableValue} per catalog row per
         * {@code (module, name)} of the run, created through the one
         * accessor — the oracle's mirror of the artifacts' program-scoped
         * catalog memoization. Written once per row and never rewritten, so
         * two reads of one cataloged export publish the identical value.
         */
        final Map<String, Value.StdlibCallableValue> stdlibCallables =
            new LinkedHashMap<>();
        /**
         * The payload-owned children: ops referenced by an owner payload's
         * child/boundary id lists (chain children, boundary children of
         * ARRAY_NEW/CALL/STDLIB_CALL/MEMBER_READ/INDEX_READ/RETURN). The
         * block walk skips them — their owner arm executes each exactly
         * once in payload order; a double execution would emit duplicated
         * effects and fail the trace pairing.
         */
        final java.util.Set<OpId> ownedChildren = new java.util.HashSet<>();
        /**
         * The class-layout resolution context (K-D11): the union of
         * every module's {@code classLayouts} — a caller's
         * {@code CLASS_NEW(SHARED_FACTORY)} payload layout resolves
         * against the owner unit's record.
         */
        final Map<ClassId, ClassLayout> classLayouts = new LinkedHashMap<>();
        /**
         * The block-owning-unit stack (innermost first): the module-init
         * walk pushes its unit, a cross-unit factory default-block
         * execution pushes the owner unit — {@link #runBlock} resolves
         * the block's membership table through the top (cross-unit
         * blocks included).
         */
        final ArrayDeque<UnitState> stateStack = new ArrayDeque<>();
        final Map<ValueId, Value> values = new HashMap<>();
        final Map<String, Cell> cells = new HashMap<>();
        /**
         * The per-invocation parameter-cell overlays, innermost first:
         * every body invocation pushes a fresh overlay holding its
         * parameter cells, so a recursive invocation re-binds its own
         * cells without corrupting the enclosing invocation's (the
         * closed cell model is keyed by binding identity — recursion
         * needs the invocation dimension).
         */
        final ArrayDeque<Map<String, Cell>> cellOverlays = new ArrayDeque<>();
        /**
         * The per-invocation value overlays, innermost first: a body
         * invocation pushes a fresh overlay so a re-executed op's result
         * slot (the same static {@code ValueId} across recursive
         * invocations) publishes per invocation — the enclosing
         * invocation's slot values stay untouched.
         */
        final ArrayDeque<Map<ValueId, Value>> valueOverlays = new ArrayDeque<>();
        final List<SemanticRuntimeModel.TraceEvent> trace = new ArrayList<>();
        final List<SemanticRuntimeModel.EffectEvent> effects = new ArrayList<>();
        final List<FunctionId> frames = new ArrayList<>();
        long sequence = 0;
        String entryResultAtom = null;
        /**
         * The per-module MODULE_INIT lifecycle records (E8): exactly one
         * {@code UNINITIALIZED -> INITIALIZING -> INITIALIZED} transition
         * per module per run, {@code FAILED} recorded by a failing walk.
         */
        final Map<ModuleId, ModuleInitLifecycle> moduleInitLifecycles =
            new LinkedHashMap<>();

        Execution(LoweredModuleUnit unit, StructuredBodyTable table, HostResponder responder) {
            this.unit = unit;
            this.table = table;
            this.responder = responder;
            this.registries = Map.of();
            UnitState entryState = new UnitState(unit, table);
            units.put(unit.moduleId(), entryState);
            entry = entryState;
            for (SemanticOp op : unit.ops()) {
                opsById.put(op.opId(), op);
            }
            // Payload-referenced children (executed exactly once by their
            // owner arm in payload order) plus boundary children of
            // MEMBER_READ/STDLIB_CALL (their owner arms' single-child
            // execution): the block walk skips these. The chain operand
            // closures (A-D2) are added on top: each ASSIGN/DELETE
            // child's operand-producing ops execute at the child's
            // position inside the chain, never at their flat block-list
            // position (the hoisted-operand interleaving the parity
            // fixtures pin).
            java.util.Set<OpId> structuralOwned =
                ChainOperandCompletion.structuralOwners(unit);
            ownedChildren.addAll(structuralOwned);
            ChainOperandCompletion.registerChainOperandOwners(unit, structuralOwned,
                ownedChildren);
            ownedChildren.addAll(entryState.ownedChildren);
            for (UnitState state : units.values()) {
                ownedChildren.addAll(state.ownedChildren);
                classLayouts.putAll(state.unit.classLayouts());
            }
            // The compiler-owned builtin Error layout (ISSUE-0619; K13 item
            // 1): the builtin class resolves in every execution's layout
            // context through the same entry the project lowering seeds, so
            // the builtin Error construction and its field ops run through
            // the closed executor views exactly like a declared class's.
            classLayouts.put(ClassId.ERROR, ClassLayout.BUILTIN_ERROR);
        }

        Execution(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                  HostResponder responder) {
            this(project, tables, Map.of(), responder);
        }

        Execution(ExecutableLoweredProject project, Map<ModuleId, StructuredBodyTable> tables,
                  Map<ModuleId, ClassFactoryRegistry> registries,
                  HostResponder responder) {
            LoweredModuleUnit entryUnit = project.modules().get(project.entryModule());
            if (entryUnit == null) {
                throw new IllegalArgumentException("the entry module is not in the closure");
            }
            this.unit = entryUnit;
            this.table = tables.get(project.entryModule());
            if (this.table == null) {
                throw new IllegalArgumentException("the entry module has no body table");
            }
            this.responder = responder;
            this.registries = Map.copyOf(registries);
            UnitState entryState = null;
            for (Map.Entry<ModuleId, LoweredModuleUnit> moduleEntry
                    : project.modules().entrySet()) {
                StructuredBodyTable moduleTable = tables.get(moduleEntry.getKey());
                if (moduleTable == null) {
                    throw new IllegalArgumentException("missing body table for module "
                        + moduleEntry.getKey());
                }
                UnitState state = new UnitState(moduleEntry.getValue(), moduleTable);
                units.put(moduleEntry.getKey(), state);
                if (moduleEntry.getKey().equals(project.entryModule())) {
                    entryState = state;
                }
            }
            entry = entryState;
            for (SemanticOp op : entryUnit.ops()) {
                opsById.put(op.opId(), op);
            }
            java.util.Set<OpId> structuralOwned =
                ChainOperandCompletion.structuralOwners(entryUnit);
            ownedChildren.addAll(structuralOwned);
            ChainOperandCompletion.registerChainOperandOwners(entryUnit, structuralOwned,
                ownedChildren);
            ownedChildren.addAll(entryState.ownedChildren);
            for (UnitState state : units.values()) {
                ownedChildren.addAll(state.ownedChildren);
                classLayouts.putAll(state.unit.classLayouts());
            }
            // The compiler-owned builtin Error layout (ISSUE-0619; K13 item
            // 1): identical in every execution's layout context.
            classLayouts.put(ClassId.ERROR, ClassLayout.BUILTIN_ERROR);
        }

        /** One module's validated execution state (ops, children, ownership). */
        private static final class UnitState {
            final LoweredModuleUnit unit;
            final StructuredBodyTable table;
            final Map<OpId, SemanticOp> opsById = new HashMap<>();
            final Map<OpId, List<SemanticOp>> childrenByParent = new HashMap<>();
            /**
             * The payload-owned children only: the chain executor's
             * operand-completion rule computes each child's producing
             * closure against its own unit's structural set — never
             * against the skip set, which already contains the chain's
             * own operand producers.
             */
            final Set<OpId> structuralOwned;
            /**
             * The block-walk skip set: {@code structuralOwned} plus every
             * chain child's operand closure (the chain arm executes
             * those at the consuming child's position).
             */
            final Set<OpId> ownedChildren;

            UnitState(LoweredModuleUnit unit, StructuredBodyTable table) {
                this.unit = unit;
                this.table = table;
                for (SemanticOp op : unit.ops()) {
                    opsById.put(op.opId(), op);
                }
                for (SemanticOp op : unit.ops()) {
                    OpId parent = op.origin().parentOpId();
                    if (parent != null) {
                        childrenByParent.computeIfAbsent(parent,
                            k -> new ArrayList<>()).add(op);
                    }
                }
                structuralOwned = ChainOperandCompletion.structuralOwners(unit);
                ownedChildren = new HashSet<>(structuralOwned);
                ChainOperandCompletion.registerChainOperandOwners(unit,
                    structuralOwned, ownedChildren);
                // The detached CLASS_DEFAULT ops are members of exactly
                // their own default blocks; those blocks execute only
                // under their triggering CLASS_NEW/CLASS_FACTORY arm, so
                // the walk skip set keeps the default ops out of any
                // block run (their own events are the owner arm's).
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        ownedChildren.add(op.opId());
                    }
                }
                // The nested source ASYNC_START of an adapter-over-async
                // task executes under its outer op's arm, never at its
                // flat block-list position.
                for (SemanticOp op : unit.ops()) {
                    if (op.kind() == SemanticOpKind.ASYNC_START) {
                        for (SemanticOp candidate : unit.ops()) {
                            if (candidate.kind() == SemanticOpKind.ASYNC_START
                                    && op.opId().equals(candidate.origin().parentOpId())) {
                                ownedChildren.add(candidate.opId());
                            }
                        }
                    }
                }
            }
        }

        /** The current value of one slot (overlays innermost-first). */
        Value valueOf(ValueId id) {
            for (Map<ValueId, Value> overlay : valueOverlays) {
                Value value = overlay.get(id);
                if (value != null) {
                    return value;
                }
            }
            return values.get(id);
        }

        /** Publishes one slot value (the innermost invocation overlay wins). */
        void putValue(ValueId id, Value value) {
            if (valueOverlays.isEmpty()) {
                values.put(id, value);
            } else {
                valueOverlays.peek().put(id, value);
            }
        }

        /** The unit state owning one op id. */
        UnitState stateOf(OpId opId) {
            UnitState state = units.get(opId.module());
            if (state == null) {
                throw new IllegalStateException("op " + opId + " names a module outside "
                    + "the executable closure (producer defect)");
            }
            return state;
        }

        /** Resolves one op id in its owning unit. */
        SemanticOp opOf(OpId opId) {
            SemanticOp op = stateOf(opId).opsById.get(opId);
            if (op == null) {
                throw new IllegalStateException("op " + opId + " is not a member of its "
                    + "validated unit (producer defect)");
            }
            return op;
        }

        /** One async task/operation state per canonical token identity. */
        static final class Task {
            final AsyncTokenId token;
            java.util.function.Supplier<Value> body;
            boolean ran;
            Value value;
            DealFailure failure;
            boolean completed;

            Task(AsyncTokenId token, java.util.function.Supplier<Value> body) {
                this.token = token;
                this.body = body;
            }
        }

        SemanticRuntimeModel.ConsumerRun report(SemanticRuntimeModel.Terminal terminal) {
            StringBuilder report = new StringBuilder();
            report.append("semantic-oracle: module=").append(unit.moduleId())
                .append(" events=").append(trace.size())
                .append(" effects=").append(effects.size())
                .append(" terminal=").append(terminal instanceof
                    SemanticRuntimeModel.Terminal.Success success
                        ? "success(" + success.resultAtom() + ")" : "deal-failure");
            return new SemanticRuntimeModel.ConsumerRun("semantic-oracle",
                unit.moduleId().path(), unit.interfaceHash(), unit.loweringContextHash(),
                trace, effects, terminal, report.toString());
        }

        // -- atoms -----------------------------------------------------------------

        String atomOf(Value value) {
            if (value == null) {
                return "missing";
            }
            return switch (value) {
                case Value.NullValue ignored -> "null";
                case Value.MissingValue ignored -> "missing";
                case Value.BoolValue bool -> "bool:" + bool.value();
                case Value.IntValue intValue -> SemanticRuntimeModel.intAtom(intValue.value());
                case Value.NumValue num -> SemanticRuntimeModel.numberAtom(num.value());
                case Value.StrValue str -> "str:" + SemanticRuntimeModel.escapeString(str.value());
                case Value.ErrorValue error -> "err:" + error.code() + ":"
                    + SemanticRuntimeModel.escapeString(error.message());
                case Value.SlotValue slot -> slot.slot() instanceof NormalizedSlot.ArraySlot array
                    ? "slot:" + array.index() + "/" + array.present() + "/" + array.append()
                    : "keyslot:" + SemanticRuntimeModel.escapeString(
                        ((NormalizedSlot.TableSlot) slot.slot()).key());
                case Value.TableValue table -> allocate(table);
                case Value.ArrayValue array -> allocate(array);
                case Value.FuncValue func -> allocate(func);
                case Value.IntrinsicValue intrinsic -> allocate(intrinsic);
                case Value.AdapterValue adapter -> allocate(adapter);
                case Value.ClassValue classValue -> allocate(classValue);
                case Value.StdlibCallableValue callable -> allocate(callable);
            };
        }

        /** The canonical token atom of an ASYNC_START/EXTERNAL_ENTRY SUCCESS. */
        String tokenAtom(AsyncTokenId token) {
            return switch (token) {
                case AsyncTokenId.Canonical canonical -> "tok:" + canonical.tokenId()
                    + ":" + canonical.owner().name();
                case AsyncTokenId.Alias alias -> "alias:" + alias.tokenId() + "->"
                    + canonicalReferent(alias.referent());
            };
        }

        /**
         * Allocation ids are assigned on first observation, not at
         * allocation time (the trace/effect/result-order normalization
         * rule): heap values reach the trace through START inputs/SUCCESS
         * outputs/effects, and the id is bound the first time the value is
         * atomized.
         */
        private final Map<Value, String> allocationIds = new java.util.IdentityHashMap<>();
        private long nextAllocationOrdinal = 1;

        private String allocate(Value heap) {
            return "ref:" + allocationIds.computeIfAbsent(heap,
                k -> String.valueOf(nextAllocationOrdinal++));
        }


        /** The atom of an op's operand value. */
        String operandAtom(SemanticOp op, int index) {
            return atomOf(valueOf(op.operands().get(index)));
        }

        String originText(SourceOrigin origin) {
            SourceSpan span = origin.span();
            return SemanticRuntimeModel.originAtom(origin.sourceId(),
                span == null ? null : span.startLine(),
                span == null ? null : span.startColumn());
        }

        // -- events -----------------------------------------------------------------

        void emitStart(SemanticOp op, List<String> inputs) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), op.origin().parentOpId(), op.kind(),
                SemanticRuntimeModel.Phase.START, op.contract().canonicalDigest(),
                inputs, null, null));
        }

        void emitSuccess(SemanticOp op, String output) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), op.origin().parentOpId(), op.kind(),
                SemanticRuntimeModel.Phase.SUCCESS, op.contract().canonicalDigest(),
                List.of(), output, null));
        }

        void emitFailure(SemanticOp op, DealFailure failure) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), op.origin().parentOpId(), op.kind(),
                SemanticRuntimeModel.Phase.FAILURE, op.contract().canonicalDigest(),
                List.of(), null, snapshot(failure)));
        }

        /** START with a structural parent override (cross-unit ENTRY execution). */
        void emitStartParented(SemanticOp op, OpId parent, List<String> inputs) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), parent, op.kind(),
                SemanticRuntimeModel.Phase.START, op.contract().canonicalDigest(),
                inputs, null, null));
        }

        /** SUCCESS with a structural parent override (cross-unit ENTRY execution). */
        void emitSuccessParented(SemanticOp op, OpId parent, String output) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), parent, op.kind(),
                SemanticRuntimeModel.Phase.SUCCESS, op.contract().canonicalDigest(),
                List.of(), output, null));
        }

        /** FAILURE with a structural parent override (cross-unit ENTRY execution). */
        void emitFailureParented(SemanticOp op, OpId parent, DealFailure failure) {
            trace.add(new SemanticRuntimeModel.TraceEvent(sequence++,
                op.opId().module().path(), op.opId(), parent, op.kind(),
                SemanticRuntimeModel.Phase.FAILURE, op.contract().canonicalDigest(),
                List.of(), null, snapshot(failure)));
        }

        SemanticRuntimeModel.ErrorSnapshot snapshot(DealFailure failure) {
            List<String> frameTexts = new ArrayList<>();
            for (FunctionId frame : failure.frames) {
                frameTexts.add(String.valueOf(frame.id()));
            }
            return new SemanticRuntimeModel.ErrorSnapshot(failure.code, failure.message,
                originText(failure.origin), failure.expected, failure.actual, frameTexts,
                failure.cause == null ? null : snapshot(failure.cause));
        }

        // -- cells -------------------------------------------------------------------

        Cell cellOf(BindingId binding, long generation, boolean create) {
            String key = binding + "#" + generation;
            if (!create) {
                for (Map<String, Cell> overlay : cellOverlays) {
                    Cell cell = overlay.get(key);
                    if (cell != null) {
                        return cell;
                    }
                }
                return cells.get(key);
            }
            if (cellOverlays.isEmpty()) {
                Cell cell = cells.get(key);
                if (cell == null) {
                    cell = new Cell(binding, generation);
                    cells.put(key, cell);
                }
                return cell;
            }
            // The innermost invocation overlay hosts fresh cells; a cell
            // already present there (an earlier re-entry of the same
            // binding identity inside one invocation) is reused.
            Map<String, Cell> top = cellOverlays.peek();
            Cell cell = top.get(key);
            if (cell == null) {
                cell = new Cell(binding, generation);
                top.put(key, cell);
            }
            return cell;
        }

        /** The binding's current (latest-generation) cell (overlays innermost-first). */
        Cell currentCellOf(BindingId binding) {
            for (Map<String, Cell> overlay : cellOverlays) {
                Cell latest = null;
                for (Cell cell : overlay.values()) {
                    if (cell.binding.equals(binding)
                            && (latest == null || cell.generation > latest.generation)) {
                        latest = cell;
                    }
                }
                if (latest != null) {
                    return latest;
                }
            }
            Cell latest = null;
            for (Cell cell : cells.values()) {
                if (cell.binding.equals(binding)) {
                    if (latest == null || cell.generation > latest.generation) {
                        latest = cell;
                    }
                }
            }
            return latest;
        }

        /**
         * Pushes one invocation's parameter-cell overlay: the body
         * block's leading parameter ALLOCs get fresh cells bound to the
         * argument values (recursion-safe — the enclosing invocation's
         * cells stay untouched).
         */
        void pushParamCells(UnitState state, BlockId bodyBlock, int paramCount,
                            List<Value> args) {
            List<OpId> bodyOps = state.table.blockOps().get(bodyBlock);
            if (bodyOps == null) {
                throw new IllegalStateException("the callee body block " + bodyBlock
                    + " has no membership row (producer defect)");
            }
            Map<String, Cell> overlay = new LinkedHashMap<>();
            for (int i = 0; i < paramCount && i < bodyOps.size(); i++) {
                SemanticOp alloc = state.opsById.get(bodyOps.get(i));
                if (alloc.kind() != SemanticOpKind.BINDING_ALLOC) {
                    throw new IllegalStateException("the callee body's leading op "
                        + alloc.opId() + " is not a BINDING_ALLOC (parameter cell)");
                }
                KindPayload.BindingAllocPayload allocPayload =
                    (KindPayload.BindingAllocPayload) alloc.payload();
                Cell cell = new Cell(allocPayload.binding(), allocPayload.generation());
                cell.value = args.get(i);
                cell.initialized = true;
                overlay.put(allocPayload.binding() + "#" + allocPayload.generation(), cell);
            }
            cellOverlays.push(overlay);
            valueOverlays.push(new LinkedHashMap<>());
        }

        /** Pops the innermost invocation's parameter-cell overlay. */
        void popParamCells() {
            cellOverlays.pop();
            valueOverlays.pop();
        }

        /** Runs one module's init walk under its owning unit state. */
        void runInit(ModuleId moduleId, LoweredModuleUnit moduleUnit) {
            UnitState moduleState = units.get(moduleId);
            if (moduleState == null) {
                throw new IllegalStateException("module " + moduleId
                    + " has no unit state in the closure (producer defect)");
            }
            stateStack.push(moduleState);
            try {
                runModuleInit(moduleUnit);
            } finally {
                stateStack.pop();
            }
        }

        /**
         * Runs one module's init walk (the E8 envelope contract): when
         * the unit carries the lowerer-produced {@code MODULE_INIT} op
         * (a module-level kind, never a member of any block), the op
         * executes as the envelope — its START, the payload init block's
         * ops nested under it, and its single terminal
         * ({@code UNINITIALIZED -> INITIALIZING -> INITIALIZED} on
         * success, {@code FAILED(error)} with no export publication on
         * failure). A hand-built unit without the op (the synthetic-unit
         * convenience surface) runs the bare init block, exactly the
         * pre-envelope behavior.
         */
        void runModuleInit(LoweredModuleUnit moduleUnit) {
            SemanticOp initOp = null;
            for (SemanticOp op : moduleUnit.ops()) {
                if (op.kind() == SemanticOpKind.MODULE_INIT) {
                    initOp = op;
                    break;
                }
            }
            if (initOp == null) {
                runBlock(moduleUnit.moduleInit().initBlock());
                return;
            }
            execute(initOp);
        }

        // -- control flow ------------------------------------------------------------

        /** Runs a block's ops in list order; transfers and failures propagate. */
        void runBlock(BlockId block) {
            UnitState state = stateStack.isEmpty() ? units.get(unit.moduleId())
                : stateStack.peek();
            runBlock(state, block);
        }

        /**
         * Runs one block of the owning unit's membership table (the
         * cross-unit surface: an owner's detached default block executes
         * through its own unit's table, never the entry module's).
         */
        void runBlock(UnitState state, BlockId block) {
            List<OpId> ops = state.table.blockOps().get(block);
            if (ops == null) {
                throw new IllegalStateException("block " + block
                    + " has no membership row (a malformed table — the production "
                    + "validator rejects this)");
            }
            for (OpId opId : ops) {
                if (ownedChildren.contains(opId)) {
                    continue; // payload-owned: the owner arm executes it once
                }
                SemanticOp op = state.opsById.get(opId);
                if (op == null) {
                    throw new IllegalStateException("op " + opId
                        + " is not a member of the validated unit");
                }
                execute(op);
            }
        }

        // =========================================================================
        // Operation execution
        // =========================================================================

        void execute(SemanticOp op) {
            List<String> inputs = new ArrayList<>();
            for (ValueId operand : op.operands()) {
                inputs.add(atomOf(valueOf(operand)));
            }
            emitStart(op, inputs);
            try {
                String output = executeKind(op);
                emitSuccess(op, output);
            } catch (ReturnSignal | LoopSignal signal) {
                emitSuccess(op, null);
                throw signal;
            } catch (DealFailure failure) {
                emitFailure(op, failure);
                throw failure;
            }
        }

        private String executeKind(SemanticOp op) {
            return switch (op.kind()) {
                case CONST -> executeConst(op);
                case UNARY -> executeUnary(op);
                case BINARY -> executeBinary(op);
                case STRING_CONCAT -> executeConcat(op);
                case ARRAY_NEW -> executeArrayNew(op);
                case TABLE_NEW -> executeTableNew(op);
                case ARRAY_LENGTH -> executeArrayLength(op);
                case MEMBER_READ -> executeMemberRead(op);
                case MEMBER_WRITE, MEMBER_DELETE, INDEX_WRITE, INDEX_DELETE,
                     FIELD_WRITE, FIELD_DELETE -> executeCommit(op);
                case INDEX_NORMALIZE -> executeNormalize(op);
                case INDEX_READ -> executeIndexRead(op);
                case OPTIONAL_READ -> executeOptionalRead(op);
                case HAS_FIELD -> executeHasField(op);
                case FIELD_READ -> executeFieldRead(op);
                case BOUNDARY -> executeBoundary(op);
                case BINDING_ALLOC -> executeBindingAlloc(op);
                case BINDING_INIT -> executeBindingInit(op);
                case BINDING_LOAD -> executeBindingLoad(op);
                case BINDING_STORE -> executeBindingStore(op);
                case CLOSURE_NEW -> executeClosureNew(op);
                case RECURSIVE_GROUP_INIT -> executeRecursiveGroupInit(op);
                case ASSIGN -> executeAssign(op);
                case DELETE -> executeDelete(op);
                case CALL -> executeCall(op);
                case EXTERNAL_ENTRY -> throw new IllegalStateException(
                    "an EXTERNAL_ENTRY executes only under its triggering caller op "
                        + "(the block walk never runs the entry record)");
                case CALLBACK_INVOKE -> throw new IllegalStateException(
                    "a CALLBACK_INVOKE executes only under the host-driven "
                        + "invokeCallback surface (the block walk never runs it)");
                case ASYNC_START -> executeAsyncStart(op);
                case AWAIT -> executeAwait(op);
                case FUNCTION_ADAPT -> executeFunctionAdapt(op);
                case ENTRY_INVOKE -> executeEntryInvoke(op);
                case EXPORT_PUBLISH -> executeExportPublish(op);
                case INTRINSIC_CALL -> executeIntrinsic(op);
                case STDLIB_CALL -> executeStdlib(op);
                case BRANCH -> executeBranch(op);
                case LOOP -> executeLoop(op);
                case FOR_EACH -> executeForEach(op);
                case TRY_CATCH -> executeTryCatch(op);
                case THROW -> executeThrow(op);
                case RETURN -> executeReturn(op);
                case BREAK -> executeBreak(op);
                case CONTINUE -> executeContinue(op);
                case DISCARD -> executeDiscard(op);
                case MODULE_IMPORT -> executeModuleImport(op);
                case EXPORT_READ -> executeExportRead(op);
                case MODULE_INIT -> executeModuleInit(op);
                case JSON_FROM_CLASS -> executeJsonFromClass(op);
                case JSON_TO_CLASS -> executeJsonToClass(op);
                case CLASS_DEFAULT -> executeClassDefaultArm(op);
                case CLASS_NEW -> executeClassNew(op);
                case CLASS_FACTORY -> throw new IllegalStateException(
                    "a CLASS_FACTORY executes only under its triggering caller's "
                        + "CLASS_NEW (the factory is a detached owner-module entry — "
                        + "the block walk never runs it)");
                default -> throw new IllegalStateException(
                    "op kind " + op.kind() + " has no oracle execution in this "
                        + "decomposition-tail domain (the carrier executes the "
                        + "EVALUATION_ORDER op set; " + op.kind()
                        + " is another epic's production)");
            };
        }

        /** Publishes an op's result value and returns its atom. */
        private String publish(SemanticOp op, Value value) {
            if (op.result() instanceof ValueId valueId) {
                putValue(valueId, value);
            }
            return atomOf(value);
        }

        private String executeConst(SemanticOp op) {
            KindPayload.ConstPayload payload = (KindPayload.ConstPayload) op.payload();
            ScalarValue scalar = payload.value();
            Value value = switch (scalar) {
                case ScalarValue.Null ignored -> Value.NullValue.INSTANCE;
                case ScalarValue.Boolean bool -> new Value.BoolValue(bool.value());
                case ScalarValue.Int intValue -> new Value.IntValue(intValue.value());
                case ScalarValue.Number number -> new Value.NumValue(number.value());
                case ScalarValue.String string -> new Value.StrValue(string.value());
            };
            return publish(op, value);
        }

        private String executeUnary(SemanticOp op) {
            KindPayload.UnaryPayload payload = (KindPayload.UnaryPayload) op.payload();
            Value input = valueOf(op.operands().get(0));
            return switch (payload.selector()) {
                case BOOL_NOT -> publish(op,
                    new Value.BoolValue(!((Value.BoolValue) input).value()));
                case INT32_NEG -> {
                    long value = ((Value.IntValue) input).value();
                    if (value == Integer.MIN_VALUE) {
                        throw int32ResultFailure(op);
                    }
                    yield publish(op, new Value.IntValue(-value));
                }
                case NUMBER_NEG -> publish(op,
                    new Value.NumValue(-((Value.NumValue) input).value()));
            };
        }

        private String executeBinary(SemanticOp op) {
            KindPayload.BinaryPayload payload = (KindPayload.BinaryPayload) op.payload();
            Value left = valueOf(op.operands().get(0));
            Value right = valueOf(op.operands().get(1));
            if (payload.selector().name().startsWith("INT32_")
                    || payload.selector().name().startsWith("NUMBER_")) {
                boolean comparison = payload.selector().name().endsWith("_EQ")
                    || payload.selector().name().endsWith("_NE")
                    || payload.selector().name().endsWith("_LT")
                    || payload.selector().name().endsWith("_LE")
                    || payload.selector().name().endsWith("_GT")
                    || payload.selector().name().endsWith("_GE");
                if (!comparison) {
                    return publish(op, arithmetic(op, payload.selector(), left, right));
                }
            }
            boolean result = ComparisonExecutor.compare(payload.selector(),
                viewOf(left), viewOf(right), payload.innerDescriptor(), payload.side());
            return publish(op, new Value.BoolValue(result));
        }

        /** The closed int32/number arithmetic rows (E8004/E8005/E8006 projections). */
        private Value arithmetic(SemanticOp op, deal.semantic.ir.BinarySelector selector,
                                 Value left, Value right) {
            return switch (selector) {
                case INT32_ADD -> int32Result(op,
                    ((Value.IntValue) left).value() + ((Value.IntValue) right).value());
                case INT32_SUB -> int32Result(op,
                    ((Value.IntValue) left).value() - ((Value.IntValue) right).value());
                case INT32_MUL -> int32Result(op,
                    ((Value.IntValue) left).value() * ((Value.IntValue) right).value());
                case INT32_DIV_TRUNC -> {
                    long divisor = ((Value.IntValue) right).value();
                    if (divisor == 0) {
                        throw registryFailure(op, FailurePolicyId.INT32_DIVISOR_THEN_RESULT,
                            null, null);
                    }
                    long dividend = ((Value.IntValue) left).value();
                    if (dividend == Integer.MIN_VALUE && divisor == -1) {
                        throw registryFailure(op, FailurePolicyId.INT32_RESULT, null, null);
                    }
                    yield int32Result(op, dividend / divisor);
                }
                case INT32_MOD_TRUNC -> {
                    long divisor = ((Value.IntValue) right).value();
                    if (divisor == 0) {
                        throw registryFailure(op, FailurePolicyId.INT32_DIVISOR_THEN_RESULT,
                            null, null);
                    }
                    yield int32Result(op, ((Value.IntValue) left).value() % divisor);
                }
                case INT32_POW -> {
                    long exponent = ((Value.IntValue) right).value();
                    if (exponent < 0) {
                        throw registryFailure(op, FailurePolicyId.INT32_EXPONENT_THEN_RESULT,
                            null, null);
                    }
                    long base = ((Value.IntValue) left).value();
                    long result = 1;
                    try {
                        for (long i = 0; i < exponent; i++) {
                            result = Math.multiplyExact(result, base);
                        }
                    } catch (ArithmeticException overflow) {
                        throw registryFailure(op, FailurePolicyId.INT32_RESULT, null, null);
                    }
                    yield int32Result(op, result);
                }
                case NUMBER_ADD -> new Value.NumValue(
                    ((Value.NumValue) left).value() + ((Value.NumValue) right).value());
                case NUMBER_SUB -> new Value.NumValue(
                    ((Value.NumValue) left).value() - ((Value.NumValue) right).value());
                case NUMBER_MUL -> new Value.NumValue(
                    ((Value.NumValue) left).value() * ((Value.NumValue) right).value());
                case NUMBER_DIV_IEEE -> new Value.NumValue(
                    ((Value.NumValue) left).value() / ((Value.NumValue) right).value());
                case NUMBER_MOD_FLOOR -> {
                    double a = ((Value.NumValue) left).value();
                    double b = ((Value.NumValue) right).value();
                    yield new Value.NumValue(a - Math.floor(a / b) * b);
                }
                case NUMBER_POW_IEEE -> new Value.NumValue(
                    Math.pow(((Value.NumValue) left).value(),
                        ((Value.NumValue) right).value()));
                default -> throw new IllegalStateException(
                    "selector " + selector + " is not an arithmetic row");
            };
        }

        /** The signed32 range projection: E8004 at the operation origin. */
        private Value int32Result(SemanticOp op, long result) {
            if (result < Integer.MIN_VALUE || result > Integer.MAX_VALUE) {
                throw registryFailure(op, FailurePolicyId.INT32_RESULT, null, null);
            }
            return new Value.IntValue(result);
        }

        /** A pinned registry-row failure at the operation origin. */
        private DealFailure registryFailure(SemanticOp op, FailurePolicyId policy,
                                            String expected, String actual) {
            BoundaryFailure failure = BoundaryFailure.fromRow(
                FailureContractRegistry.row(policy), 0, expected, actual,
                new LinkedHashMap<>(), null);
            return DealFailure.of(failure, op.origin(), List.copyOf(frames));
        }

        private DealFailure int32ResultFailure(SemanticOp op) {
            return registryFailure(op, FailurePolicyId.INT32_RESULT, null, null);
        }

        /** Identity wrappers for heap values (record equality never decides
         *  reference identity). */
        private final Map<Value, Object> refIdentities = new java.util.IdentityHashMap<>();

        private Object refIdentity(Value heap) {
            return refIdentities.computeIfAbsent(heap, k -> new Object());
        }

        /** The runtime value → closed comparison operand view (B-D1). */
        ComparisonOperandView viewOf(Value value) {
            return switch (value) {
                case Value.NullValue ignored -> ComparisonOperandView.Null.INSTANCE;
                case Value.MissingValue ignored -> ComparisonOperandView.Missing.INSTANCE;
                case Value.BoolValue bool -> new ComparisonOperandView.Boolean(bool.value());
                case Value.IntValue intValue ->
                    new ComparisonOperandView.Int((int) intValue.value());
                case Value.NumValue num -> new ComparisonOperandView.Number(num.value());
                case Value.StrValue str -> new ComparisonOperandView.String(
                    (UnicodeScalars.Valid) UnicodeScalars.validate(str.value()));
                case Value.TableValue table -> new ComparisonOperandView.Ref(refIdentity(table));
                case Value.ArrayValue array -> new ComparisonOperandView.Ref(refIdentity(array));
                case Value.FuncValue func -> new ComparisonOperandView.Ref(refIdentity(func));
                case Value.IntrinsicValue intrinsic ->
                    new ComparisonOperandView.Ref(refIdentity(intrinsic));
                case Value.StdlibCallableValue callable ->
                    // The in-target cataloged callable (M4): a heap value whose
                    // identity is its memoized allocation, exactly like the
                    // intrinsic and closure carriers — two reads of one catalog
                    // row compare equal, two distinct rows compare unequal, and
                    // both production artifacts compare the identical memoized
                    // object (REFERENCE_EQ -> `l == r`).
                    new ComparisonOperandView.Ref(refIdentity(callable));
                default -> throw new IllegalStateException(
                    "value " + value.getClass().getSimpleName()
                        + " is not a comparison operand view");
            };
        }

        private String executeConcat(SemanticOp op) {
            KindPayload.StringConcatPayload payload =
                (KindPayload.StringConcatPayload) op.payload();
            StringBuilder out = new StringBuilder();
            for (ValueId fragment : payload.fragments()) {
                out.append(((Value.StrValue) valueOf(fragment)).value());
            }
            return publish(op, new Value.StrValue(out.toString()));
        }

        private String executeArrayNew(SemanticOp op) {
            KindPayload.ArrayNewPayload payload = (KindPayload.ArrayNewPayload) op.payload();
            List<Value> elements = new ArrayList<>();
            for (int i = 0; i < payload.values().size(); i++) {
                ValueId valueId = payload.values().get(i);
                OpId boundaryId = payload.elementBoundaryOpIds().get(i);
                SemanticOp boundary = opOf(boundaryId);
                Value checked = runBoundaryChild(boundary, valueOf(valueId),
                    BoundaryContext.element(i + 1));
                elements.add(checked);
            }
            return publish(op, new Value.ArrayValue(elements, payload.elementDescriptor()));
        }

        private String executeTableNew(SemanticOp op) {
            KindPayload.TableNewPayload payload = (KindPayload.TableNewPayload) op.payload();
            LinkedHashMap<String, Value> entries = new LinkedHashMap<>();
            for (KindPayload.TableEntry entry : payload.entries()) {
                entries.put(entry.key(), valueOf(entry.value()));
            }
            return publish(op, new Value.TableValue(entries));
        }

        private String executeArrayLength(SemanticOp op) {
            KindPayload.ArrayLengthPayload payload =
                (KindPayload.ArrayLengthPayload) op.payload();
            Value.ArrayValue array = (Value.ArrayValue) valueOf(payload.arrayValue());
            return publish(op, new Value.IntValue(array.elements().size()));
        }

        /**
         * MEMBER_READ: the missing-aware read, then its
         * CONTEXTUAL_TABLE_READ boundary child (missing→nullable-null /
         * E8001 via the contextual decision).
         */
        private String executeMemberRead(SemanticOp op) {
            KindPayload.MemberReadPayload payload = (KindPayload.MemberReadPayload) op.payload();
            Value.TableValue table = (Value.TableValue) valueOf(payload.table());
            Value read = table.entries().get(payload.key());
            if (read == null) {
                read = Value.MissingValue.INSTANCE;
            }
            SemanticOp boundary = singleChild(op);
            if (boundary == null) {
                return publish(op, read);
            }
            RuntimeDescriptor descriptor =
                ((KindPayload.BoundaryPayload) boundary.payload()).descriptor();
            Value checked = runBoundaryChild(boundary, read, BoundaryContext.none());
            return contextualReadDecision(op, checked, descriptor);
        }

        /**
         * OPTIONAL_READ (the CONTAINERS_AND_STRINGS extras): the raw read
         * value pre-maps the internal missing to language null before the
         * present branch is validated (the closed table's optional-read
         * rule) — the op's CONTEXTUAL_TABLE_READ boundary child then runs
         * over the pre-mapped value (present null passes the nullable
         * descriptor; a present wrong-kind value projects the pinned
         * E8001). A payload with no value slot (present=false) is the
         * statically absent slot: language null, no validation.
         */
        private String executeOptionalRead(SemanticOp op) {
            KindPayload.OptionalReadPayload payload =
                (KindPayload.OptionalReadPayload) op.payload();
            Value input = payload.value() == null
                ? Value.MissingValue.INSTANCE : valueOf(payload.value());
            Value preMapped = input instanceof Value.MissingValue
                ? Value.NullValue.INSTANCE : input;
            SemanticOp boundary = singleChild(op);
            if (boundary == null) {
                return publish(op, preMapped);
            }
            RuntimeDescriptor descriptor =
                ((KindPayload.BoundaryPayload) boundary.payload()).descriptor();
            Value checked = runBoundaryChild(boundary, preMapped, BoundaryContext.none());
            return contextualReadDecision(op, checked, descriptor);
        }

        /**
         * HAS_FIELD: the presence boolean of one checked receiver key —
         * present (present null included) → true, absent → false. The
         * table-presence half realizes through the value model's keyed
         * entries; the class-instance half (the presence map of a
         * generated instance) is the CLASSES family's production and has
         * no oracle representation in this domain yet.
         */
        private String executeHasField(SemanticOp op) {
            KindPayload.HasFieldPayload payload =
                (KindPayload.HasFieldPayload) op.payload();
            Value receiver = valueOf(payload.receiver());
            if (receiver instanceof Value.TableValue table) {
                return publish(op,
                    new Value.BoolValue(table.entries().containsKey(payload.key())));
            }
            if (receiver instanceof Value.ClassValue classValue) {
                // The class-instance presence half (K-D7): the
                // presence map of the generated instance — a present
                // field (present null included) is present, a missing
                // field is absent. The instance's states parallel its
                // declared layout's declaration order (the construction
                // executor pins the parallel-array discipline).
                ClassLayout layout = classLayouts.get(classValue.classId());
                if (layout == null || layout.fields().size() != classValue.fields().size()) {
                    throw new IllegalStateException("HAS_FIELD " + op.opId()
                        + " class instance " + classValue.classId()
                        + " has no matching layout in the resolution context "
                        + "(producer defect)");
                }
                for (int i = 0; i < layout.fields().size(); i++) {
                    if (layout.fields().get(i).name().equals(payload.key())) {
                        return publish(op, new Value.BoolValue(
                            classValue.fields().get(i)
                                instanceof Value.ClassFieldState.Present));
                    }
                }
                throw new IllegalStateException("HAS_FIELD " + op.opId() + " key '"
                    + payload.key() + "' is not a declared field of "
                    + classValue.classId() + " (producer defect)");
            }
            throw new IllegalStateException("HAS_FIELD " + op.opId() + " receiver "
                + payload.receiver() + " resolves to " + atomOf(receiver) + ": the table"
                + "-presence half of the CONTAINERS_AND_STRINGS extras admits keyed table"
                + " receivers and the class-instance half admits generated class"
                + " instances (a receiver outside those carriers is a producer defect)");
        }

        // =========================================================================
        // The class-construction ops (CLASSES step 8, E5 core):
        // CLASS_DEFAULT/CLASS_NEW/CLASS_FACTORY delegation to the closed
        // {@link ClassOpsExecutor} (construction order, factory transfer,
        // field presence) — no ad-hoc fork of the pinned D16 order.
        // =========================================================================

        /**
         * The block execution returning the original oracle value.
         */
        private Value executeDefaultBlockValue(SemanticOp defaultOp) {
            KindPayload.ClassDefaultPayload payload =
                (KindPayload.ClassDefaultPayload) defaultOp.payload();
            UnitState state = stateOf(defaultOp.opId());
            stateStack.push(state);
            try {
                runBlock(payload.defaultBlock());
            } finally {
                stateStack.pop();
            }
            if (!(defaultOp.result() instanceof ValueId resultId)) {
                throw new IllegalStateException("CLASS_DEFAULT " + defaultOp.opId()
                    + " publishes no ValueId result (producer defect)");
            }
            Value produced = valueOf(resultId);
            if (produced == null) {
                throw new IllegalStateException("CLASS_DEFAULT " + defaultOp.opId()
                    + " default block produced no value in its result slot "
                    + resultId + " (producer defect)");
            }
            return produced;
        }

        /**
         * CLASS_DEFAULT reached directly by the block walk — a producer
         * defect (the detached default blocks execute only under their
         * triggering construction; the walk skip set keeps them out of
         * the walk).
         */
        private String executeClassDefaultArm(SemanticOp op) {
            throw new IllegalStateException("a CLASS_DEFAULT executes only under its "
                + "triggering CLASS_NEW/CLASS_FACTORY (the default op is a member of "
                + "exactly its own detached default block — the block walk never "
                + "runs it); reaching executeClassDefaultArm is a producer defect");
        }

        /**
         * JSON_FROM_CLASS — the generated {@code C$fromJson} walk (E7/K-D8),
         * delegating to the closed {@link ClassOpsExecutor} with the
         * production algorithm seam ({@link JsonClassAlgorithmAdapter}) and
         * the op's per-site {@code CLASS_DEFAULT} children. The per-site
         * children are the layout's required-present defaulted fields'
         * {@code CLASS_DEFAULT} ops in declaration order — the same list
         * the lowerer records in the produced {@code JsonDefaultChildTable}
         * (the record is a lowering-result fact, so the closed set is
         * derived from the unit here: one {@code CLASS_DEFAULT} op per
         * {@code (classId, field)}). The walk returns language null on
         * every listed failure — never a DEAL failure, never a partial
         * instance.
         */
        private String executeJsonFromClass(SemanticOp op) {
            KindPayload.JsonFromClassPayload payload =
                (KindPayload.JsonFromClassPayload) op.payload();
            UnitState state = stateOf(op.opId());
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            priorValues.put(payload.jsonString(),
                executorValueOf(valueOf(payload.jsonString())));
            Map<OpId, SemanticOp> defaultOps = new LinkedHashMap<>();
            for (SemanticOp candidate : state.unit.ops()) {
                if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                    defaultOps.put(candidate.opId(), candidate);
                }
            }
            List<OpId> defaultChildIds = jsonDefaultChildrenOf(state,
                payload.layout());
            Value produced = oracleValueOf(ClassOpsExecutor.executeJsonFromClass(op,
                priorValues, defaultChildIds, defaultOps, classLayouts,
                JsonClassAlgorithmAdapter.parser(), nestedClassFactory(op),
                bodyRunner(op)));
            return publish(op, produced);
        }

        /**
         * JSON_TO_CLASS — the generated {@code C$toJson} walk (E7/K-D10),
         * delegating to the closed {@link ClassOpsExecutor} with the
         * production stringify seam. The first declaration-order failure
         * projects {@code JSON_TO_ERROR} (E8001
         * {@code value at {fieldPath} is not JSON serializable: {actual}})
         * at the op's origin; success publishes the deterministic
         * RFC-8259 text.
         */
        private String executeJsonToClass(SemanticOp op) {
            KindPayload.JsonToClassPayload payload =
                (KindPayload.JsonToClassPayload) op.payload();
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            priorValues.put(payload.classValue(),
                executorValueOf(valueOf(payload.classValue())));
            ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> outcome =
                ClassOpsExecutor.executeJsonToClass(op, priorValues, classLayouts,
                    JsonClassAlgorithmAdapter.stringifier(), op.origin());
            return switch (outcome) {
                case ClassOpsExecutor.Outcome.Success<ClassOpsExecutor.Value> success ->
                    publish(op, oracleValueOf(success.value()));
                case ClassOpsExecutor.Outcome.Failure<ClassOpsExecutor.Value> failure ->
                    throw DealFailure.of(failure.failure().failure(),
                        failure.failure().origin(), List.copyOf(frames));
            };
        }

        /**
         * The per-site {@code CLASS_DEFAULT} children of one
         * {@code JSON_FROM_CLASS} op in declaration order: for every
         * required-present layout field that carries a declared default
         * (exactly one {@code CLASS_DEFAULT} op per
         * {@code (classId, field)}) the op id; optional fields' never-run
         * defaults are excluded (K-D8 step 5).
         */
        private List<OpId> jsonDefaultChildrenOf(UnitState state, ClassLayout layout) {
            List<OpId> children = new ArrayList<>();
            for (ClassLayout.FieldLayout field : layout.fields()) {
                if (!field.required()) {
                    continue;
                }
                for (SemanticOp candidate : state.unit.ops()) {
                    if (candidate.kind() != SemanticOpKind.CLASS_DEFAULT) {
                        continue;
                    }
                    KindPayload.ClassDefaultPayload defaultPayload =
                        (KindPayload.ClassDefaultPayload) candidate.payload();
                    if (defaultPayload.classId().equals(layout.classId())
                            && defaultPayload.field().equals(field.name())) {
                        children.add(candidate.opId());
                        break;
                    }
                }
            }
            return children;
        }

        /**
         * The nested-class defaults seam of the JSON_FROM_CLASS walk
         * (K-D5 trigger (b)): the nested class's {@code CLASS_FACTORY}
         * entry resolves in the closure (one factory per exported class;
         * a non-exported class carries no factory and a nested decode of
         * it is a producer defect, never executed), its default children
         * run in the declaring module's scope with their own events, and
         * the factory's events parent to the triggering JSON op (the
         * cross-unit K-D12 parent).
         */
        private ClassOpsExecutor.NestedClassFactory nestedClassFactory(SemanticOp triggering) {
            return (classId, providedFields) -> {
                SemanticOp factoryOp = null;
                for (UnitState candidateState : units.values()) {
                    for (SemanticOp candidate : candidateState.unit.ops()) {
                        if (candidate.kind() != SemanticOpKind.CLASS_FACTORY) {
                            continue;
                        }
                        if (((KindPayload.ClassFactoryPayload) candidate.payload())
                                .classId().equals(classId)) {
                            factoryOp = candidate;
                            break;
                        }
                    }
                    if (factoryOp != null) {
                        break;
                    }
                }
                if (factoryOp == null) {
                    throw new IllegalStateException("a nested JSON decode of " + classId
                        + " resolves no CLASS_FACTORY entry in the closure (the nested "
                        + "defaults seam requires the owner factory — producer defect, "
                        + "never executed)");
                }
                UnitState ownerState = stateOf(factoryOp.opId());
                Map<OpId, SemanticOp> ownerDefaultOps = new LinkedHashMap<>();
                for (SemanticOp candidate : ownerState.unit.ops()) {
                    if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                        ownerDefaultOps.put(candidate.opId(), candidate);
                    }
                }
                ClassOpsExecutor.BodyRunner runner = defaultOp -> {
                    emitStart(defaultOp, List.of());
                    Value oracleProduced;
                    try {
                        oracleProduced = executeDefaultBlockValue(defaultOp);
                    } catch (DealFailure failure) {
                        emitFailure(defaultOp, failure);
                        throw failure;
                    }
                    ClassOpsExecutor.Value produced = executorValueOf(oracleProduced);
                    publish(defaultOp, oracleProduced);
                    emitSuccess(defaultOp, atomOf(oracleProduced));
                    return produced;
                };
                emitStartParented(factoryOp, triggering.opId(), List.of());
                ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> outcome;
                try {
                    outcome = ClassOpsExecutor.executeClassFactory(factoryOp, triggering,
                        ownerDefaultOps, classLayouts, providedFields, runner);
                } catch (DealFailure failure) {
                    emitFailureParented(factoryOp, triggering.opId(), failure);
                    throw failure;
                }
                if (!(outcome instanceof ClassOpsExecutor.Outcome.Success
                        <ClassOpsExecutor.Value> success
                        && success.value() instanceof ClassOpsExecutor.Value.Class)) {
                    throw new IllegalStateException("CLASS_FACTORY " + factoryOp.opId()
                        + " produced " + outcome + " — the pinned factory returns "
                        + "exactly its internal default-filled transfer instance "
                        + "(producer defect)");
                }
                ClassOpsExecutor.Value.Class transferInstance =
                    (ClassOpsExecutor.Value.Class) success.value();
                Value transferValue = oracleValueOf(transferInstance);
                if (factoryOp.result() instanceof ValueId factoryResult) {
                    putValue(factoryResult, transferValue);
                }
                emitSuccessParented(factoryOp, triggering.opId(), atomOf(transferValue));
                return transferInstance;
            };
        }

        /**
         * CLASS_NEW — the closed K-D4/D16 construction in emitted order:
         * provided values resolve in literal order (they completed before
         * the op), default application in declaration order (LOCAL, or the
         * owner's CLASS_FACTORY transfer with the factory's events parented
         * to this caller op — cross-unit K-D12), extra-key rejection first
         * in provided-source order (E8007), provided-field application in
         * declaration order, field validation in declaration order through
         * the boundary children, and the tag-last publication. Zero return
         * boundaries. A failure publishes no partial instance.
         */
        private String executeClassNew(SemanticOp op) {
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) op.payload();
            UnitState state = stateOf(op.opId());
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                priorValues.put(field.valueOpId(),
                    executorValueOf(valueOf(field.valueOpId())));
            }
            Map<OpId, SemanticOp> defaultOps = new LinkedHashMap<>();
            Map<OpId, SemanticOp> boundaryOps = new LinkedHashMap<>();
            for (SemanticOp candidate : state.unit.ops()) {
                if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                    defaultOps.put(candidate.opId(), candidate);
                }
                if (candidate.kind() == SemanticOpKind.BOUNDARY) {
                    boundaryOps.put(candidate.opId(), candidate);
                }
            }
            ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> outcome;
            switch (payload.defaultOwner()) {
                case LOCAL -> outcome = ClassOpsExecutor.executeClassNewLocal(op,
                    priorValues, defaultOps, boundaryOps, classLayouts,
                    checkRunner(op, payload, boundaryOps, null),
                    bodyRunner(op));
                case SHARED_FACTORY -> {
                    ModuleId ownerModule = new ModuleId(payload.classId().modulePath());
                    ClassFactoryRegistry registry = registries.get(ownerModule);
                    if (registry == null) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " SHARED_FACTORY owner " + ownerModule
                            + " has no ClassFactoryRegistry in the executable closure "
                            + "(an owner outside the shared route is never executed "
                            + "here — producer defect)");
                    }
                    OpId factoryOpId = registry.factoryFor(payload.classFactoryRef());
                    if (factoryOpId == null) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " classFactoryRef " + payload.classFactoryRef()
                            + " does not resolve in the owner's registry "
                            + "(producer defect)");
                    }
                    SemanticOp factoryOp = opOf(factoryOpId);
                    if (factoryOp.kind() != SemanticOpKind.CLASS_FACTORY) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " resolves factory op " + factoryOpId + " of kind "
                            + factoryOp.kind() + " (producer defect)");
                    }
                    KindPayload.ClassFactoryPayload factoryPayload =
                        (KindPayload.ClassFactoryPayload) factoryOp.payload();
                    if (!factoryPayload.classId().equals(payload.classId())) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " resolves a factory of " + factoryPayload.classId()
                            + " (producer defect)");
                    }
                    UnitState ownerState = stateOf(factoryOpId);
                    Map<OpId, SemanticOp> ownerDefaultOps = new LinkedHashMap<>();
                    for (SemanticOp candidate : ownerState.unit.ops()) {
                        if (candidate.kind() == SemanticOpKind.CLASS_DEFAULT) {
                            ownerDefaultOps.put(candidate.opId(), candidate);
                        }
                    }
                    Set<String> providedNames = new LinkedHashSet<>();
                    for (KindPayload.ProvidedField field : payload.providedFields()) {
                        providedNames.add(field.name());
                    }
                    // Stage A — the recorded factory execution: the owner
                    // CLASS_DEFAULT children run exactly once per
                    // triggering construction attempt in the declaring
                    // module's scope, with their own events (the original
                    // produced values atomized); the factory's events
                    // parent to this caller op (cross-unit).
                    Map<OpId, ClassOpsExecutor.Value> captured = new LinkedHashMap<>();
                    ClassOpsExecutor.BodyRunner recordingRunner = defaultOp -> {
                        emitStart(defaultOp, List.of());
                        Value oracleProduced;
                        try {
                            oracleProduced = executeDefaultBlockValue(defaultOp);
                        } catch (DealFailure failure) {
                            emitFailure(defaultOp, failure);
                            throw failure;
                        }
                        ClassOpsExecutor.Value produced = executorValueOf(oracleProduced);
                        publish(defaultOp, oracleProduced);
                        emitSuccess(defaultOp, atomOf(oracleProduced));
                        captured.put(defaultOp.opId(), produced);
                        return produced;
                    };
                    emitStartParented(factoryOp, op.opId(), List.of());
                    ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> transfer;
                    try {
                        transfer = ClassOpsExecutor.executeClassFactory(factoryOp, op,
                            ownerDefaultOps, classLayouts, providedNames, recordingRunner);
                    } catch (DealFailure failure) {
                        emitFailureParented(factoryOp, op.opId(), failure);
                        throw failure;
                    }
                    if (!(transfer instanceof ClassOpsExecutor.Outcome.Success
                            <ClassOpsExecutor.Value> success
                            && success.value()
                                instanceof ClassOpsExecutor.Value.Class transferInstance)) {
                        throw new IllegalStateException("CLASS_FACTORY " + factoryOp.opId()
                            + " produced " + transfer + " — the pinned factory returns "
                            + "exactly its internal default-filled transfer instance "
                            + "(producer defect)");
                    }
                    Value transferValue = oracleValueOf(transferInstance);
                    if (!(transferValue instanceof Value.ClassValue transferClassValue)) {
                        throw new IllegalStateException("CLASS_FACTORY " + factoryOp.opId()
                            + " transfer converted to a non-instance value "
                            + "(producer defect)");
                    }
                    putValue((ValueId) factoryOp.result(), transferClassValue);
                    emitSuccessParented(factoryOp, op.opId(), atomOf(transferClassValue));
                    // Stage B — the executor's pinned completion (extra-key,
                    // overlay, boundaries, tag) with a replaying runner
                    // returning the recorded default values (the blocks ran
                    // once in stage A; the replay is pure bookkeeping).
                    ClassOpsExecutor.BodyRunner replayRunner = defaultOp -> {
                        ClassOpsExecutor.Value value = captured.get(defaultOp.opId());
                        if (value == null) {
                            throw new IllegalStateException("CLASS_FACTORY "
                                + factoryOp.opId() + " default child " + defaultOp.opId()
                                + " was not captured in the recorded pass "
                                + "(producer defect)");
                        }
                        return value;
                    };
                    outcome = ClassOpsExecutor.executeClassNewSharedFactory(op,
                        priorValues, registry, ownerState.opsById, boundaryOps,
                        classLayouts, checkRunner(op, payload, boundaryOps,
                            (ValueId) factoryOp.result()), replayRunner);
                }
                case HOST_DEFAULTS, FFI_PLAN ->
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " carries defaultOwner " + payload.defaultOwner()
                        + ": the declaration-class owners are the project lowering's"
                        + " class registration seeds (ISSUE-0631) and their construction"
                        + " is not executed in this slice — a fail-closed producer"
                        + " defect, never executed and never default-evaluated");
                case BUILTIN_DEFAULTS -> {
                    if (!ClassId.ERROR.equals(payload.classId())) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " carries defaultOwner BUILTIN_DEFAULTS for class "
                            + payload.classId() + ": the builtin-defaults owner is"
                            + " admissible only for the builtin Error class"
                            + " (producer defect)");
                    }
                    // The builtin Error construction (ISSUE-0619; K13 items
                    // 2-4): the provided values complete in payload order
                    // through the existing check runner, the omitted fields
                    // take the compiler constant empty string, and the
                    // published value is the canonical Error value.
                    outcome = ClassOpsExecutor.executeClassNewBuiltinDefaults(op,
                        priorValues, boundaryOps, classLayouts,
                        checkRunner(op, payload, boundaryOps, null));
                }
                default -> throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " carries defaultOwner " + payload.defaultOwner()
                    + " outside the executable owners (producer defect)");
            }
            return switch (outcome) {
                case ClassOpsExecutor.Outcome.Success<ClassOpsExecutor.Value> success ->
                    publish(op, oracleValueOf(success.value()));
                case ClassOpsExecutor.Outcome.Failure<ClassOpsExecutor.Value> failure ->
                    throw DealFailure.of(failure.failure().failure(),
                        failure.failure().origin(), List.copyOf(frames));
            };
        }

        /**
         * The construction's body runner (K-D4 step 2): one default
         * block per triggering attempt with the default op's own START
         * and terminal events around it — a block failure emits the
         * default op's FAILURE and propagates (the caller op's wrapper
         * emits its own FAILURE). The events atomize the block's
         * original produced value (never a re-converted copy), so the
         * value's allocation id is the one the produced op published.
         */
        private ClassOpsExecutor.BodyRunner bodyRunner(SemanticOp op) {
            return defaultOp -> {
                emitStart(defaultOp, List.of());
                Value oracleProduced;
                try {
                    oracleProduced = executeDefaultBlockValue(defaultOp);
                } catch (DealFailure failure) {
                    emitFailure(defaultOp, failure);
                    throw failure;
                }
                ClassOpsExecutor.Value produced = executorValueOf(oracleProduced);
                publish(defaultOp, oracleProduced);
                emitSuccess(defaultOp, atomOf(oracleProduced));
                return produced;
            };
        }

        /**
         * The construction's boundary-check runner (K-D4 step 5): each
         * field boundary child runs once in payload (declaration) order
         * through the closed {@link BoundaryExecutor} with its own START
         * and terminal events; the checked input is the original value of
         * the child's recorded input slot (a {@code CLASS_DEFAULT_FIELD}
         * child of a SHARED_FACTORY construction reads the named field of
         * the transferred instance — the K-D4 extraction rule).
         */
        private ClassOpsExecutor.BoundaryCheckRunner checkRunner(SemanticOp op,
                KindPayload.ClassNewPayload payload, Map<OpId, SemanticOp> boundaryOps,
                ValueId factoryResult) {
            final int[] boundaryIndex = {0};
            return (boundaryPayload, input) -> {
                List<KindPayload.FieldBoundary> entries = payload.fieldBoundaries();
                if (boundaryIndex[0] >= entries.size()) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " ran more field boundaries than its payload lists "
                        + "(producer defect)");
                }
                KindPayload.FieldBoundary entry = entries.get(boundaryIndex[0]++);
                SemanticOp boundary = boundaryOps.get(entry.boundaryOpId());
                if (boundary == null) {
                    throw new IllegalStateException("CLASS_NEW " + op.opId()
                        + " field boundary " + entry.boundaryOpId() + " does not resolve "
                        + "(producer defect)");
                }
                Value oracleInput;
                if (entry.kind() == BoundaryKind.CLASS_DEFAULT_FIELD
                        && factoryResult != null
                        && factoryResult.equals(boundaryPayload.input())) {
                    Value transferred = valueOf(factoryResult);
                    if (!(transferred instanceof Value.ClassValue transferInstance)) {
                        throw new IllegalStateException("CLASS_NEW " + op.opId()
                            + " CLASS_DEFAULT_FIELD input " + factoryResult
                            + " resolves to a non-instance value (producer defect)");
                    }
                    oracleInput = classFieldOf(op, transferInstance, entry.field());
                } else {
                    oracleInput = valueOf(boundaryPayload.input());
                }
                try {
                    Value checked = runBoundaryChild(boundary, oracleInput,
                        BoundaryContext.none());
                    return new ClassOpsExecutor.BoundaryResult.Pass(
                        executorValueOf(checked));
                } catch (DealFailure failure) {
                    return new ClassOpsExecutor.BoundaryResult.Fail(
                        new BoundaryFailure(boundary.failurePolicy(),
                            DiagnosticCode.fromCode(failure.code), failure.message,
                            failure.expected, failure.actual, Map.of(), null));
                }
            };
        }

        /** The present value of one named declaration-order field of a class instance. */
        private Value classFieldOf(SemanticOp op, Value.ClassValue instance,
                                   String fieldName) {
            ClassLayout layout = classLayouts.get(instance.classId());
            if (layout == null || layout.fields().size() != instance.fields().size()) {
                throw new IllegalStateException("CLASS_NEW " + op.opId()
                    + " instance " + instance.classId()
                    + " has no matching layout in the resolution context "
                    + "(producer defect)");
            }
            for (int i = 0; i < layout.fields().size(); i++) {
                if (layout.fields().get(i).name().equals(fieldName)) {
                    return switch (instance.fields().get(i)) {
                        case Value.ClassFieldState.Present present -> present.value();
                        case Value.ClassFieldState.Missing ignored ->
                            throw new IllegalStateException("CLASS_NEW " + op.opId()
                                + " reads field '" + fieldName + "' of a transferred "
                                + "instance whose field is missing (producer defect)");
                    };
                }
            }
            throw new IllegalStateException("CLASS_NEW " + op.opId() + " field '"
                + fieldName + "' is not declared in " + instance.classId()
                + " (producer defect)");
        }

        /**
         * The run-global conversion caches between the oracle value
         * model and the executor's closed view (identity-keyed): a heap
         * value converted twice yields the same view (and back), so a
         * class field stores the original value's identity — never a
         * re-converted copy with a fresh allocation id.
         */
        final IdentityHashMap<Value, ClassOpsExecutor.Value> executorViews =
            new IdentityHashMap<>();
        final IdentityHashMap<ClassOpsExecutor.Value, Value> oracleOriginals =
            new IdentityHashMap<>();

        /** The oracle runtime value → the executor's closed value view. */
        private ClassOpsExecutor.Value executorValueOf(Value value) {
            if (value instanceof Value.NullValue || value instanceof Value.MissingValue
                    || value instanceof Value.BoolValue || value instanceof Value.IntValue
                    || value instanceof Value.NumValue || value instanceof Value.StrValue
                    || value instanceof Value.IntrinsicValue
                    || value instanceof Value.SlotValue) {
                return convertExecutorView(value);
            }
            ClassOpsExecutor.Value cached = executorViews.get(value);
            if (cached == null) {
                cached = convertExecutorView(value);
                executorViews.put(value, cached);
                oracleOriginals.put(cached, value);
            }
            return cached;
        }

        /** The executor's closed value view → the oracle runtime value. */
        private Value oracleValueOf(ClassOpsExecutor.Value value) {
            if (value instanceof ClassOpsExecutor.Value.Null
                    || value instanceof ClassOpsExecutor.Value.Missing
                    || value instanceof ClassOpsExecutor.Value.Bool
                    || value instanceof ClassOpsExecutor.Value.Int
                    || value instanceof ClassOpsExecutor.Value.Number
                    || value instanceof ClassOpsExecutor.Value.String) {
                return convertOracleView(value);
            }
            Value cached = oracleOriginals.get(value);
            if (cached == null) {
                cached = convertOracleView(value);
                oracleOriginals.put(value, cached);
                if (cached instanceof Value.ErrorValue errorValue) {
                    // The builtin Error carrier's closed class view: the
                    // conversion caches stay symmetric (the field ops and the
                    // commit observe the same view), exactly like the class
                    // instance caches.
                    executorViews.put(errorValue, value);
                }
            }
            return cached;
        }

        /** The uncached oracle → executor conversion. */
        private ClassOpsExecutor.Value convertExecutorView(Value value) {
            return switch (value) {
                case Value.NullValue ignored -> ClassOpsExecutor.Value.Null.INSTANCE;
                case Value.MissingValue ignored -> ClassOpsExecutor.Value.Missing.INSTANCE;
                case Value.BoolValue bool ->
                    new ClassOpsExecutor.Value.Bool(bool.value());
                case Value.IntValue intValue ->
                    new ClassOpsExecutor.Value.Int((int) intValue.value());
                case Value.NumValue num ->
                    new ClassOpsExecutor.Value.Number(num.value());
                case Value.StrValue str ->
                    ClassOpsExecutor.Value.string(str.value());
                case Value.TableValue table -> {
                    SemanticTable<ClassOpsExecutor.Value> entries =
                        new SemanticTable<>();
                    for (Map.Entry<String, Value> entry : table.entries().entrySet()) {
                        entries.put(entry.getKey(), executorValueOf(entry.getValue()));
                    }
                    yield new ClassOpsExecutor.Value.Table(entries);
                }
                case Value.ArrayValue array -> {
                    List<ClassOpsExecutor.Value> elements = new ArrayList<>();
                    for (Value element : array.elements()) {
                        elements.add(executorValueOf(element));
                    }
                    yield new ClassOpsExecutor.Value.Array(
                        SemanticArray.of(elements));
                }
                case Value.FuncValue func ->
                    new ClassOpsExecutor.Value.Function(func.signature());
                case Value.AdapterValue adapter ->
                    new ClassOpsExecutor.Value.Function(adapter.signature());
                case Value.StdlibCallableValue callable ->
                    new ClassOpsExecutor.Value.Function(callable.descriptor());
                case Value.ClassValue classValue ->
                    new ClassOpsExecutor.Value.Class(classValue.classId(),
                        classValue.fields().stream()
                            .<ClassOpsExecutor.FieldState>map(field ->
                                field instanceof Value.ClassFieldState.Present present
                                    ? new ClassOpsExecutor.FieldState.Present(
                                        executorValueOf(present.value()))
                                    : ClassOpsExecutor.FieldState.Missing.INSTANCE)
                            .toList());
                case Value.ErrorValue error ->
                    // The builtin Error carrier's closed class view (K13 item
                    // 5): both declared fields present in declaration order —
                    // the field ops read and write them through the same
                    // closed view as any declared class.
                    new ClassOpsExecutor.Value.Class(ClassId.ERROR, List.of(
                        new ClassOpsExecutor.FieldState.Present(
                            ClassOpsExecutor.Value.string(error.code())),
                        new ClassOpsExecutor.FieldState.Present(
                            ClassOpsExecutor.Value.string(error.message()))));
                case Value.IntrinsicValue ignored ->
                    new ClassOpsExecutor.Value.Function(new RuntimeDescriptor.Func(
                        List.of(), RuntimeDescriptor.Number.INSTANCE, false));
                case Value.SlotValue ignored ->
                    throw new IllegalStateException("a normalize-computed slot is never "
                        + "a construction input (producer defect)");
            };
        }

        /** The uncached executor → oracle conversion. */
        private Value convertOracleView(ClassOpsExecutor.Value value) {
            return switch (value) {
                case ClassOpsExecutor.Value.Null ignored -> Value.NullValue.INSTANCE;
                case ClassOpsExecutor.Value.Missing ignored -> Value.MissingValue.INSTANCE;
                case ClassOpsExecutor.Value.Bool bool ->
                    new Value.BoolValue(bool.value());
                case ClassOpsExecutor.Value.Int intValue ->
                    new Value.IntValue(intValue.value());
                case ClassOpsExecutor.Value.Number number ->
                    new Value.NumValue(number.value());
                case ClassOpsExecutor.Value.String string -> {
                    UnicodeScalars.ScalarString scalar = string.scalar();
                    if (scalar instanceof UnicodeScalars.Valid valid) {
                        yield new Value.StrValue(valid.carrier());
                    }
                    throw new IllegalStateException("an INVALID_UNICODE string "
                        + "crossed the class-construction view — the closed view "
                        + "carries no invalid carrier (producer defect in this "
                        + "slice's corpus)");
                }
                case ClassOpsExecutor.Value.Table table -> {
                    LinkedHashMap<String, Value> entries = new LinkedHashMap<>();
                    for (String key : table.table().keys()) {
                        SemanticTable.Lookup<ClassOpsExecutor.Value> lookup =
                            table.table().get(key);
                        entries.put(key, oracleValueOf(
                            lookup instanceof SemanticTable.Lookup.Present
                                <ClassOpsExecutor.Value> present
                                ? present.value()
                                : ClassOpsExecutor.Value.Missing.INSTANCE));
                    }
                    yield new Value.TableValue(entries);
                }
                case ClassOpsExecutor.Value.Array array -> {
                    List<Value> elements = new ArrayList<>();
                    for (int i = 0; i < array.array().size(); i++) {
                        elements.add(oracleValueOf(array.array().elementAt(i)));
                    }
                    // The closed view carries no element descriptor; the
                    // oracle's array values never consult the descriptor
                    // at execution (boundaries and atoms read elements
                    // only), so a construction-crossed array carries the
                    // neutral descriptor.
                    yield new Value.ArrayValue(elements,
                        RuntimeDescriptor.String.INSTANCE);
                }
                case ClassOpsExecutor.Value.Function function ->
                    new Value.FuncValue(null, function.signature(), Map.of());
                case ClassOpsExecutor.Value.Class classValue -> {
                    if (ClassId.ERROR.equals(classValue.classId())) {
                        // The builtin Error view converts back to the Error
                        // value — never to a generic class value (K13 item 5).
                        yield errorValueOf(classValue);
                    }
                    yield new Value.ClassValue(classValue.classId(),
                        classValue.fields().stream()
                            .<Value.ClassFieldState>map(field ->
                                field instanceof ClassOpsExecutor.FieldState.Present present
                                    ? new Value.ClassFieldState.Present(
                                        oracleValueOf(present.value()))
                                    : Value.ClassFieldState.Missing.INSTANCE)
                            .toList());
                }
            };
        }

        /**
         * The builtin Error value of one closed executor class view (K13
         * item 5): exactly two present string fields in declaration order;
         * any other shape is a producer defect.
         */
        private Value.ErrorValue errorValueOf(ClassOpsExecutor.Value.Class classValue) {
            if (classValue.fields().size() != 2
                    || !(classValue.fields().get(0)
                        instanceof ClassOpsExecutor.FieldState.Present codeState)
                    || !(classValue.fields().get(1)
                        instanceof ClassOpsExecutor.FieldState.Present messageState)
                    || !(codeState.value() instanceof ClassOpsExecutor.Value.String code)
                    || !(messageState.value()
                        instanceof ClassOpsExecutor.Value.String message)) {
                throw new IllegalStateException("the builtin Error class view "
                    + "carries " + classValue.fields() + ": the closed view is"
                    + " exactly two present string fields (code, message) — a"
                    + " producer defect");
            }
            if (!(code.scalar() instanceof UnicodeScalars.Valid codeScalar)
                    || !(message.scalar()
                        instanceof UnicodeScalars.Valid messageScalar)) {
                throw new IllegalStateException("the builtin Error class view"
                    + " carries an invalid-unicode scalar (producer defect)");
            }
            return new Value.ErrorValue(codeScalar.carrier(), messageScalar.carrier());
        }

        /** The single child op parented to {@code op}, or null. */
        private SemanticOp singleChild(SemanticOp op) {
            List<SemanticOp> children = stateOf(op.opId()).childrenByParent.get(op.opId());
            if (children == null || children.isEmpty()) {
                return null;
            }
            if (children.size() != 1) {
                throw new IllegalStateException("op " + op.opId() + " has "
                    + children.size() + " children; a single child was expected");
            }
            return children.get(0);
        }

        /**
         * A commit op (MEMBER_WRITE/DELETE, INDEX_WRITE/DELETE,
         * FIELD_WRITE/DELETE): exactly one storage mutation over resolved
         * references, never re-evaluating a source expression. The class
         * field commits consume the chain's resolved receiver slot and
         * delegate their closed semantics (nominal receiver boundary,
         * field boundary, presence-preserving store) to
         * {@link ClassOpsExecutor}; the committed state replaces the
         * receiver's declaration-order field state in place, so every
         * reference to the instance observes the commit exactly like the
         * target carriers.
         */
        private String executeCommit(SemanticOp op) {
            switch (op.payload()) {
                case KindPayload.MemberWritePayload payload -> {
                    Value.TableValue table = (Value.TableValue) valueOf(payload.table());
                    table.entries().put(payload.key(), valueOf(payload.value()));
                }
                case KindPayload.MemberDeletePayload payload -> {
                    Value.TableValue table = (Value.TableValue) valueOf(payload.table());
                    table.entries().remove(payload.key());
                }
                case KindPayload.IndexWritePayload payload -> {
                    Value container = valueOf(payload.container());
                    NormalizedSlot slot = ((Value.SlotValue) valueOf(payload.slot())).slot();
                    commitIndexWrite(container, slot, valueOf(payload.value()));
                }
                case KindPayload.IndexDeletePayload payload -> {
                    Value container = valueOf(payload.container());
                    NormalizedSlot slot = ((Value.SlotValue) valueOf(payload.slot())).slot();
                    commitIndexDelete(container, slot);
                }
                case KindPayload.FieldWritePayload payload -> {
                    List<SemanticOp> boundaries = List.of(
                        boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT),
                        boundaryChildOfKind(op, BoundaryKind.CLASS_FIELD_ASSIGNMENT));
                    Map<ValueId, ClassOpsExecutor.Value> priorValues =
                        fieldCommitValues(op, payload.classValue(), payload.value());
                    applyFieldCommit(op, payload.classValue(),
                        ClassOpsExecutor.executeFieldWrite(op, priorValues,
                            boundaries.get(0), boundaries.get(1), classLayouts,
                            sequentialBoundaryRunner(boundaries)));
                }
                case KindPayload.FieldDeletePayload payload -> {
                    List<SemanticOp> boundaries = List.of(
                        boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT));
                    Map<ValueId, ClassOpsExecutor.Value> priorValues =
                        fieldCommitValues(op, payload.classValue(), null);
                    applyFieldCommit(op, payload.classValue(),
                        ClassOpsExecutor.executeFieldDelete(op, priorValues,
                            boundaries.get(0), classLayouts,
                            sequentialBoundaryRunner(boundaries)));
                }
                default -> throw new IllegalStateException(
                    "commit op payload " + op.payload().getClass().getSimpleName());
            }
            return null;
        }

        /**
         * The class field commit's resolved operands: the receiver slot
         * exactly once (never re-evaluated) and the stored value slot for
         * a write — the executor's prior-value map. An unresolved slot is
         * a producer defect, fail closed before any boundary runs.
         */
        private Map<ValueId, ClassOpsExecutor.Value> fieldCommitValues(
                SemanticOp op, ValueId receiverId, ValueId storedId) {
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            priorValues.put(receiverId, executorValueOf(resolvedSlot(op, receiverId)));
            if (storedId != null) {
                priorValues.put(storedId, executorValueOf(resolvedSlot(op, storedId)));
            }
            return priorValues;
        }

        /**
         * The published value of one resolved chain slot: the commit
         * consumes the slot's already-completed value and never
         * re-evaluates a source expression; an unpublished slot is a
         * producer defect (a malformed chain), fail closed.
         */
        private Value resolvedSlot(SemanticOp op, ValueId id) {
            Value value = valueOf(id);
            if (value == null) {
                throw new IllegalStateException(op.kind() + " " + op.opId()
                    + " consumes the unresolved slot " + id + ": the chain's resolved "
                    + "receiver/operand slots complete before the commit runs "
                    + "(producer defect)");
            }
            return value;
        }

        /**
         * Applies one class field commit outcome: SUCCESS replaces the
         * receiver instance's named declaration-order field state in
         * place (the fresh updated instance the executor publishes is
         * applied to the same oracle instance every reference observes),
         * FAILURE rethrows the boundary's failure at the op origin. The
         * builtin Error receiver commits its own carrier's field in place
         * and rebinds the conversion caches to the updated view (K13's
         * field surface).
         */
        private void applyFieldCommit(SemanticOp op, ValueId receiverId,
                ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> outcome) {
            Value receiver = valueOf(receiverId);
            switch (receiver) {
                case Value.ClassValue classValue -> {
                    switch (outcome) {
                        case ClassOpsExecutor.Outcome.Success
                                <ClassOpsExecutor.Value> success ->
                            applyInstanceState(classValue, success.value());
                        case ClassOpsExecutor.Outcome.Failure
                                <ClassOpsExecutor.Value> failure ->
                            throw DealFailure.of(failure.failure().failure(),
                                failure.failure().origin(), List.copyOf(frames));
                    }
                }
                case Value.ErrorValue errorValue -> {
                    switch (outcome) {
                        case ClassOpsExecutor.Outcome.Success
                                <ClassOpsExecutor.Value> success ->
                            applyErrorState(errorValue, success.value());
                        case ClassOpsExecutor.Outcome.Failure
                                <ClassOpsExecutor.Value> failure ->
                            throw DealFailure.of(failure.failure().failure(),
                                failure.failure().origin(), List.copyOf(frames));
                    }
                }
                default -> throw new IllegalStateException(op.kind() + " " + op.opId()
                    + " receiver " + receiverId + " resolves to " + atomOf(receiver)
                    + ": the class field commit consumes a resolved class instance "
                    + "(producer defect)");
            }
        }

        /**
         * The builtin Error field commit (K13's field surface): the
         * published updated view's named field value is written into the
         * carrier in place — every alias of the instance observes the
         * commit — and the conversion caches are rebound to the updated
         * view, so the next delegation converts the committed state (never
         * a stale pre-commit view). The field payload's name selects the
         * carrier field; the receiver boundary already proved the
         * @/Error identity and the field boundary the declared string
         * descriptor.
         */
        private void applyErrorState(Value.ErrorValue receiver,
                                     ClassOpsExecutor.Value updated) {
            if (!(updated instanceof ClassOpsExecutor.Value.Class updatedClass)
                    || !ClassId.ERROR.equals(updatedClass.classId())
                    || updatedClass.fields().size() != 2) {
                throw new IllegalStateException("a builtin Error field commit"
                    + " produced " + updated + ": the pinned outcome is the updated"
                    + " @/Error instance with its two declaration-order fields"
                    + " (producer defect)");
            }
            Value.ErrorValue state = errorValueOf(updatedClass);
            receiver.writeField("code", state.code());
            receiver.writeField("message", state.message());
            executorViews.put(receiver, updated);
            oracleOriginals.put(updated, receiver);
        }

        /**
         * FIELD_READ — the presence-aware class member read (K-D6): the
         * receiver resolves from the value lookup exactly once (never
         * re-evaluated) and the op's two pinned boundary children run in
         * order — the nominal {@code UNTYPED_CLASS_INPUT} receiver
         * boundary, then the {@code OPTIONAL_FIELD_READ} boundary over
         * the pre-mapped read (a missing field pre-maps to language null
         * before the boundary; present null stays distinguishable from
         * missing through the presence states); SUCCESS publishes the
         * boundary-checked value. The closed presence/read/wrap
         * discipline is {@link ClassOpsExecutor#executeFieldRead}, never
         * forked here.
         */
        private String executeFieldRead(SemanticOp op) {
            KindPayload.FieldReadPayload payload =
                (KindPayload.FieldReadPayload) op.payload();
            List<SemanticOp> boundaries = List.of(
                boundaryChildOfKind(op, BoundaryKind.UNTYPED_CLASS_INPUT),
                boundaryChildOfKind(op, BoundaryKind.OPTIONAL_FIELD_READ));
            Map<ValueId, ClassOpsExecutor.Value> priorValues = new LinkedHashMap<>();
            priorValues.put(payload.classValue(),
                executorValueOf(resolvedSlot(op, payload.classValue())));
            ClassOpsExecutor.Outcome<ClassOpsExecutor.Value> outcome =
                ClassOpsExecutor.executeFieldRead(op, priorValues, boundaries.get(0),
                    boundaries.get(1), classLayouts, sequentialBoundaryRunner(boundaries));
            return switch (outcome) {
                case ClassOpsExecutor.Outcome.Success<ClassOpsExecutor.Value> success ->
                    publish(op, oracleValueOf(success.value()));
                case ClassOpsExecutor.Outcome.Failure<ClassOpsExecutor.Value> failure ->
                    throw DealFailure.of(failure.failure().failure(),
                        failure.failure().origin(), List.copyOf(frames));
            };
        }

        /**
         * The pinned boundary child of one field op (K-D12): the child
         * whose recorded {@code parentOpId} is the field op and whose
         * closed kind matches. A missing or duplicated pinned child is a
         * producer defect, fail closed before any execution.
         */
        private SemanticOp boundaryChildOfKind(SemanticOp op, BoundaryKind kind) {
            List<SemanticOp> children = stateOf(op.opId()).childrenByParent.get(op.opId());
            SemanticOp match = null;
            if (children != null) {
                for (SemanticOp child : children) {
                    if (child.kind() == SemanticOpKind.BOUNDARY
                            && ((KindPayload.BoundaryPayload) child.payload()).kind()
                                == kind) {
                        if (match != null) {
                            throw new IllegalStateException(op.kind() + " " + op.opId()
                                + " parents two " + kind + " boundary children: the "
                                + "pinned shape carries exactly one (producer defect)");
                        }
                        match = child;
                    }
                }
            }
            if (match == null) {
                throw new IllegalStateException(op.kind() + " " + op.opId()
                    + " has no " + kind + " boundary child: the pinned field-op shape "
                    + "carries it parented to the op (producer defect)");
            }
            return match;
        }

        /**
         * The field ops' boundary-check runner: the executor's runner
         * seam carries the boundary payload; the pinned children run in
         * their declared order with their own START/terminal events and
         * the executor-visible checked value flows back.
         */
        private ClassOpsExecutor.BoundaryCheckRunner sequentialBoundaryRunner(
                List<SemanticOp> boundaries) {
            final int[] index = {0};
            return (boundaryPayload, input) -> {
                if (index[0] >= boundaries.size()) {
                    throw new IllegalStateException("a field-op boundary run exceeds "
                        + "the pinned child list (producer defect)");
                }
                SemanticOp boundary = boundaries.get(index[0]++);
                try {
                    Value checked = runBoundaryChild(boundary, oracleValueOf(input),
                        BoundaryContext.none());
                    return new ClassOpsExecutor.BoundaryResult.Pass(
                        executorValueOf(checked));
                } catch (DealFailure failure) {
                    return new ClassOpsExecutor.BoundaryResult.Fail(
                        new BoundaryFailure(boundary.failurePolicy(),
                            DiagnosticCode.fromCode(failure.code), failure.message,
                            failure.expected, failure.actual, Map.of(), null));
                }
            };
        }

        /**
         * Applies one committed instance state to the receiver's live
         * storage: the declaration-order field states are replaced in
         * place (every alias of the instance observes the commit) and the
         * executor-view cache is rebound to the updated instance, so the
         * next delegation converts the committed state — never a stale
         * pre-commit view.
         */
        private void applyInstanceState(Value.ClassValue receiver,
                                        ClassOpsExecutor.Value updated) {
            if (!(updated instanceof ClassOpsExecutor.Value.Class updatedClass)) {
                throw new IllegalStateException("a field commit produced " + updated
                    + ": the pinned outcome is the updated instance "
                    + "(producer defect)");
            }
            if (!updatedClass.classId().equals(receiver.classId())
                    || updatedClass.fields().size() != receiver.fields().size()) {
                throw new IllegalStateException("a field commit produced "
                    + updatedClass.classId() + " with "
                    + updatedClass.fields().size() + " fields for the receiver "
                    + receiver.classId() + " with " + receiver.fields().size()
                    + " (producer defect)");
            }
            for (int i = 0; i < updatedClass.fields().size(); i++) {
                ClassOpsExecutor.FieldState state = updatedClass.fields().get(i);
                Value.ClassFieldState applied = switch (state) {
                    case ClassOpsExecutor.FieldState.Present present ->
                        new Value.ClassFieldState.Present(
                            oracleValueOf(present.value()));
                    case ClassOpsExecutor.FieldState.Missing ignored ->
                        Value.ClassFieldState.Missing.INSTANCE;
                };
                receiver.replaceField(i, applied);
            }
            // The conversion caches stay symmetric: the updated instance
            // view is the receiver's view (a later delegation converts the
            // committed state, and a boundary round-trip atomizes the same
            // instance the receiver references — never a fresh copy).
            executorViews.put(receiver, updated);
            oracleOriginals.put(updated, receiver);
        }

        /** The array/table commit mutation (slot mechanics of the carrier). */
        private void commitIndexWrite(Value container, NormalizedSlot slot, Value value) {
            switch (slot) {
                case NormalizedSlot.ArraySlot array -> {
                    Value.ArrayValue target = (Value.ArrayValue) container;
                    if (array.append()) {
                        target.elements().add(value);
                    } else {
                        target.elements().set(array.index(), value);
                    }
                }
                case NormalizedSlot.TableSlot table ->
                    ((Value.TableValue) container).entries().put(table.key(), value);
            }
        }

        private void commitIndexDelete(Value container, NormalizedSlot slot) {
            switch (slot) {
                case NormalizedSlot.ArraySlot array -> {
                    Value.ArrayValue target = (Value.ArrayValue) container;
                    if (array.index() < target.elements().size()) {
                        target.elements().set(array.index(), Value.MissingValue.INSTANCE);
                    }
                    // index == length: the nil write at the append slot is a
                    // no-op on a dense array (A-D4).
                }
                case NormalizedSlot.TableSlot table ->
                    ((Value.TableValue) container).entries().remove(table.key());
            }
        }

        private String executeNormalize(SemanticOp op) {
            KindPayload.IndexNormalizePayload payload =
                (KindPayload.IndexNormalizePayload) op.payload();
            Value rawKey = valueOf(payload.rawKey());
            Value currentLength = valueOf(payload.currentLength());
            NormalizedSlot slot = switch (payload.mode()) {
                case ARRAY_READ, ARRAY_WRITE -> NormalizedSlot.arraySlot(payload.mode(),
                    (int) ((Value.IntValue) rawKey).value(),
                    (int) ((Value.IntValue) currentLength).value());
                case TABLE_READ, TABLE_WRITE -> NormalizedSlot.tableSlot(payload.mode(),
                    ((Value.StrValue) rawKey).value());
            };
            return publish(op, new Value.SlotValue(slot));
        }

        private String executeIndexRead(SemanticOp op) {
            KindPayload.IndexReadPayload payload = (KindPayload.IndexReadPayload) op.payload();
            Value container = valueOf(payload.container());
            NormalizedSlot slot = ((Value.SlotValue) valueOf(payload.slot())).slot();
            SemanticOp boundary = opOf(payload.elementBoundaryOpId());
            RuntimeDescriptor descriptor = ((KindPayload.BoundaryPayload) boundary.payload())
                .descriptor();
            switch (slot) {
                case NormalizedSlot.ArraySlot array -> {
                    Value.ArrayValue target = (Value.ArrayValue) container;
                    int index = array.index();
                    Value read;
                    if (index < 0) {
                        read = Value.MissingValue.INSTANCE; // E8002 before any read
                    } else if (index < target.elements().size()) {
                        read = target.elements().get(index);
                    } else {
                        read = Value.MissingValue.INSTANCE;
                    }
                    Value checked = runBoundaryChild(boundary, read,
                        BoundaryContext.arrayIndex(index));
                    if (checked instanceof Value.MissingValue
                            && descriptor instanceof RuntimeDescriptor.Nullable) {
                        checked = Value.NullValue.INSTANCE;
                    }
                    // A missing read publishes missing: the consuming
                    // contextual boundary/operand decides E8001/null
                    // (the comparison operands' missing≡null rule, the
                    // declaration boundary's E8001 projection).
                    return publish(op, checked);
                }
                case NormalizedSlot.TableSlot table -> {
                    Value.TableValue target = (Value.TableValue) container;
                    Value read = target.entries().get(table.key());
                    if (read == null) {
                        read = Value.MissingValue.INSTANCE;
                    }
                    Value checked = runBoundaryChild(boundary, read, BoundaryContext.none());
                    return contextualReadDecision(op, checked, descriptor);
                }
            }
        }

        /**
         * The read's contextual decision (the ARRAY_ELEMENT_READ/
         * CONTEXTUAL_TABLE_READ cell passes the missing view through; the
         * contextual boundary decides E8001/null): a missing value against
         * a nullable descriptor maps to language null; against a
         * non-nullable descriptor it projects the pinned E8001
         * {@code expected {expected}, got missing} at the read origin.
         */
        private String contextualReadDecision(SemanticOp op, Value checked,
                                              RuntimeDescriptor descriptor) {
            if (checked instanceof Value.MissingValue
                    && !(descriptor instanceof RuntimeDescriptor.Nullable)) {
                BoundaryFailure failure = BoundaryFailure.fromRow(
                    FailureContractRegistry.row(FailurePolicyId.TYPE_DESCRIPTOR), 0,
                    descriptor.canonicalSpecText(),
                    ActualKind.canonicalToken(ActualKind.MISSING, null),
                    new LinkedHashMap<>(), null);
                throw DealFailure.of(failure, op.origin(), List.copyOf(frames));
            }
            if (checked instanceof Value.MissingValue) {
                checked = Value.NullValue.INSTANCE;
            }
            return publish(op, checked);
        }

        /**
         * Executes one BOUNDARY child with its own START/terminal events.
         */
        Value runBoundaryChild(SemanticOp boundary, Value input, BoundaryContext context) {
            List<String> inputs = List.of(atomOf(input));
            emitStart(boundary, inputs);
            KindPayload.BoundaryPayload payload =
                (KindPayload.BoundaryPayload) boundary.payload();
            BoundaryValueView view = viewOfValue(input);
            BoundaryOutcome outcome;
            try {
                outcome = BoundaryExecutor.execute(boundary.failurePolicy(),
                    payload.descriptor(), view, context, payload.realization());
            } catch (BoundaryExecutor.Defect defect) {
                throw new IllegalStateException("boundary " + boundary.opId()
                    + " has no executor projection: " + defect.getMessage());
            }
            return switch (outcome) {
                case BoundaryOutcome.Pass pass -> {
                    Value result = valueOfView(pass.value(), input);
                    emitSuccess(boundary, atomOf(result));
                    yield result;
                }
                case BoundaryOutcome.Fail fail -> {
                    DealFailure failure = DealFailure.of(fail.failure(), boundary.origin(),
                        List.copyOf(frames));
                    emitFailure(boundary, failure);
                    throw failure;
                }
            };
        }

        /** The runtime value → closed boundary view. */
        private BoundaryValueView viewOfValue(Value value) {
            return switch (value) {
                case Value.NullValue ignored -> BoundaryValueView.nullView();
                case Value.MissingValue ignored -> BoundaryValueView.of(ActualKind.MISSING);
                case Value.BoolValue bool -> BoundaryValueView.of(ActualKind.BOOLEAN);
                case Value.IntValue intValue -> BoundaryValueView.ofInt(intValue.value());
                case Value.NumValue num -> BoundaryValueView.ofNumber(num.value());
                case Value.StrValue str -> {
                    UnicodeScalars.ScalarString scalar = UnicodeScalars.validate(str.value());
                    yield scalar instanceof UnicodeScalars.Valid
                        ? BoundaryValueView.of(ActualKind.STRING)
                        : BoundaryValueView.of(ActualKind.INVALID_UNICODE);
                }
                case Value.TableValue table -> BoundaryValueView.of(ActualKind.TABLE);
                case Value.ErrorValue error ->
                    // The builtin Error carrier's closed boundary view
                    // (ISSUE-0619; K13 item 5): the canonical @/Error class
                    // atom, so the descriptor-atom check of an @/Error
                    // boundary matches and the class value crosses it
                    // unchanged. The value's own atom stays the closed
                    // err:<code>:<message> form and its actual kind stays
                    // class:@builtin/Error.
                    BoundaryValueView.ofClass(ClassId.ERROR.text());
                case Value.FuncValue func -> BoundaryValueView.ofFunction(func.signature());
                case Value.AdapterValue adapter ->
                    BoundaryValueView.ofFunction(adapter.signature());
                case Value.IntrinsicValue intrinsic ->
                    BoundaryValueView.ofFunction(new RuntimeDescriptor.Func(List.of(),
                        RuntimeDescriptor.Number.INSTANCE, false));
                case Value.StdlibCallableValue callable ->
                    BoundaryValueView.ofFunction(callable.descriptor());
                case Value.ArrayValue array -> {
                    List<BoundaryValueView> elements = new ArrayList<>();
                    for (Value element : array.elements()) {
                        elements.add(viewOfValue(element));
                    }
                    yield BoundaryValueView.ofArray(elements);
                }
                case Value.ClassValue classValue ->
                    BoundaryValueView.ofClass(classValue.classId().text());
                case Value.SlotValue slot -> BoundaryValueView.of(ActualKind.INT);
            };
        }

        /** The passed boundary view → runtime value (missing→null was pre-mapped). */
        private Value valueOfView(BoundaryValueView view, Value original) {
            if (view.kind() == ActualKind.MISSING) {
                return Value.MissingValue.INSTANCE;
            }
            if (view.kind() == ActualKind.NULL) {
                return Value.NullValue.INSTANCE;
            }
            return original;
        }

        /** A free BOUNDARY op: the check over its completed operand (no events here). */
        private String executeBoundary(SemanticOp op) {
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) op.payload();
            Value input = valueOf(payload.input());
            BoundaryOutcome outcome;
            try {
                outcome = BoundaryExecutor.execute(op.failurePolicy(), payload.descriptor(),
                    viewOfValue(input), BoundaryContext.none(), payload.realization());
            } catch (BoundaryExecutor.Defect defect) {
                throw new IllegalStateException("boundary " + op.opId()
                    + " has no executor projection: " + defect.getMessage());
            }
            return switch (outcome) {
                case BoundaryOutcome.Pass pass -> publish(op, valueOfView(pass.value(), input));
                case BoundaryOutcome.Fail fail ->
                    throw DealFailure.of(fail.failure(), op.origin(), List.copyOf(frames));
            };
        }

        private String executeBindingAlloc(SemanticOp op) {
            KindPayload.BindingAllocPayload payload =
                (KindPayload.BindingAllocPayload) op.payload();
            cellOf(payload.binding(), payload.generation(), true);
            return null;
        }

        private String executeBindingInit(SemanticOp op) {
            KindPayload.BindingInitPayload payload =
                (KindPayload.BindingInitPayload) op.payload();
            Cell cell = cellOf(payload.binding(), payload.generation(), true);
            Value value = valueOf(payload.value());
            if (value == null) {
                // An intrinsic function identity (int()/number() as
                // first-class values — the producer-less identity slot).
                value = new Value.IntrinsicValue("intrinsic");
                putValue(payload.value(), value);
            }
            cell.value = value;
            cell.initialized = true;
            return null;
        }

        private String executeBindingLoad(SemanticOp op) {
            KindPayload.BindingLoadPayload payload =
                (KindPayload.BindingLoadPayload) op.payload();
            Cell cell = cellOf(payload.binding(), payload.generation(), false);
            if (cell == null || !cell.initialized) {
                throw new IllegalStateException("binding load of uninitialized cell "
                    + payload.binding() + "#" + payload.generation() + " at op "
                    + op.opId() + " in " + op.origin().sourceId());
            }
            return publish(op, cell.value);
        }

        private String executeBindingStore(SemanticOp op) {
            KindPayload.BindingStorePayload payload =
                (KindPayload.BindingStorePayload) op.payload();
            Cell cell = cellOf(payload.binding(), payload.generation(), true);
            cell.value = valueOf(payload.value());
            cell.initialized = true;
            return null;
        }

        private String executeClosureNew(SemanticOp op) {
            KindPayload.ClosureNewPayload payload =
                (KindPayload.ClosureNewPayload) op.payload();
            Map<BindingId, Cell> captures = new HashMap<>();
            for (BindingId binding : payload.captures()) {
                Cell current = currentCellOf(binding);
                if (current == null) {
                    throw new IllegalStateException("closure capture of unknown binding "
                        + binding);
                }
                captures.put(binding, current);
            }
            Value.FuncValue closure = new Value.FuncValue(payload.function(),
                payload.signature(), captures);
            FunctionExecutionBinding binding = bindingOf((ValueId) op.result());
            if (binding != null) {
                bindingsByValue.put(closure, binding);
            }
            return publish(op, closure);
        }

        /**
         * RECURSIVE_GROUP_INIT (E8, atomic publication): phase 1
         * allocates every member's identity — a fresh {@link Value.FuncValue}
         * capturing the member cells — before any publication, keyed to
         * the member's pre-assigned allocation identity (the registry's
         * one {@code LoweredBody} per member); phase 2 publishes the
         * member closures to the member binding cells in declaration
         * order in one ordered sequence. No member observes a partially
         * initialized group: no member body runs at group execution, all
         * captures resolve before the first publication, and every
         * execution publishes fresh identities.
         */
        private String executeRecursiveGroupInit(SemanticOp op) {
            KindPayload.RecursiveGroupInitPayload payload =
                (KindPayload.RecursiveGroupInitPayload) op.payload();
            UnitState state = stateOf(op.opId());
            if (payload.bindings().size() != payload.functions().size()) {
                throw new IllegalStateException("RECURSIVE_GROUP_INIT " + op.opId()
                    + " carries " + payload.bindings().size() + " bindings but "
                    + payload.functions().size() + " member functions "
                    + "(producer defect; the payload pins one entry per member)");
            }
            // Phase 0: every member cell exists before any capture
            // resolves (a sibling capture references a member cell).
            List<Cell> memberCells = new ArrayList<>();
            for (BindingId binding : payload.bindings()) {
                memberCells.add(cellOf(binding, 0, true));
            }
            // Phase 1: allocate every member identity first (fresh per
            // execution) — no publication yet.
            List<Value.FuncValue> members = new ArrayList<>();
            for (int i = 0; i < payload.functions().size(); i++) {
                FunctionId functionId = payload.functions().get(i);
                LoweredFunction function = state.unit.functions().get(functionId);
                if (function == null) {
                    throw new IllegalStateException("group member " + functionId
                        + " has no LoweredFunction record (producer defect)");
                }
                Map<BindingId, Cell> captures = new HashMap<>();
                for (BindingId binding : function.captures()) {
                    Cell current = currentCellOf(binding);
                    if (current == null) {
                        throw new IllegalStateException("group member capture of "
                            + "unknown binding " + binding);
                    }
                    captures.put(binding, current);
                }
                Value.FuncValue closure = new Value.FuncValue(functionId,
                    function.descriptor(), captures);
                ValueId identity = memberIdentityOf(state, functionId);
                FunctionExecutionBinding binding = bindingOf(identity);
                if (binding != null) {
                    bindingsByValue.put(closure, binding);
                }
                members.add(closure);
            }
            // Phase 2: publish in one ordered sequence.
            for (int i = 0; i < payload.bindings().size(); i++) {
                Cell cell = memberCells.get(i);
                cell.value = members.get(i);
                cell.initialized = true;
            }
            return null;
        }

        /**
         * The pre-assigned allocation identity of one group member: the
         * {@link FunctionAllocationIdentity} key whose registered
         * {@code LoweredBody} names the member's function id (B4/B5 —
         * the one registration per member the publication phase writes
         * into the member binding cell).
         */
        private ValueId memberIdentityOf(UnitState state, FunctionId functionId) {
            for (Map.Entry<FunctionAllocationIdentity, FunctionExecutionBinding> entry
                    : state.unit.functionBindings().entrySet()) {
                if (entry.getValue() instanceof FunctionExecutionBinding.LoweredBody body
                        && body.functionId().equals(functionId)) {
                    return new ValueId(entry.getKey().id());
                }
            }
            throw new IllegalStateException("group member " + functionId
                + " has no registered LoweredBody binding (producer defect; "
                + "every RECURSIVE_GROUP_INIT member registers exactly one "
                + "binding keyed by its pre-assigned allocation identity)");
        }

        /** ASSIGN: children in payload order; the committed value result is pre-published. */
        private String executeAssign(SemanticOp op) {
            KindPayload.AssignPayload payload = (KindPayload.AssignPayload) op.payload();
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opOf(childId);
                completeChainOperands(child);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) child.payload();
                    BoundaryContext context = chainBoundaryContext(op, boundaryPayload.kind());
                    Value input = valueOf(boundaryPayload.input());
                    runBoundaryChild(child, input, context);
                } else {
                    execute(child);
                }
            }
            Value committed = null;
            if (op.result() instanceof ValueId valueId) {
                committed = valueOf(valueId);
            }
            return committed == null ? null : atomOf(committed);
        }

        /**
         * The chain executor's boundary-context supply (A-D4): the array
         * assignment/delete boundaries receive {@code {index, length}}
         * from the chain's already-completed normalize slot and length
         * children (both precede the boundary in payload order); every
         * other chain boundary runs with no context.
         */
        private BoundaryContext chainBoundaryContext(SemanticOp chain,
                                                     deal.semantic.ir.BoundaryKind kind) {
            if (kind != deal.semantic.ir.BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                    && kind != deal.semantic.ir.BoundaryKind.ARRAY_ELEMENT_DELETE) {
                return BoundaryContext.none();
            }
            NormalizedSlot.ArraySlot array = null;
            int length = -1;
            List<OpId> children = switch (chain.payload()) {
                case KindPayload.AssignPayload assign -> assign.childOps();
                case KindPayload.DeletePayload delete -> delete.childOps();
                default -> List.of();
            };
            Map<OpId, SemanticOp> ops = stateOf(chain.opId()).opsById;
            for (OpId childId : children) {
                SemanticOp child = ops.get(childId);
                if (child.kind() == SemanticOpKind.INDEX_NORMALIZE
                        && child.result() instanceof ValueId normalizeResult) {
                    array = (NormalizedSlot.ArraySlot)
                        ((Value.SlotValue) valueOf(normalizeResult)).slot();
                } else if (child.kind() == SemanticOpKind.ARRAY_LENGTH
                        && child.result() instanceof ValueId lengthResult) {
                    length = (int) ((Value.IntValue) valueOf(lengthResult)).value();
                }
            }
            if (array == null || length < 0) {
                throw new IllegalStateException("an array chain boundary lacks its "
                    + "normalize slot/length facts (a malformed chain — the production "
                    + "protocol rejects this)");
            }
            return BoundaryContext.writeBounds(array.index(), length);
        }

        /**
         * The chain executor's boundary-context supply (A-D4): the array
         * assignment/delete boundaries receive {@code {index, length}}
         * from the chain's normalize slot and length values; every other
         * chain boundary runs with no context.
         */
        private BoundaryContext chainBoundaryContext(deal.semantic.ir.BoundaryKind kind,
                                                     Value.SlotValue slot, Value length) {
            if (kind == deal.semantic.ir.BoundaryKind.ARRAY_ELEMENT_ASSIGNMENT
                    || kind == deal.semantic.ir.BoundaryKind.ARRAY_ELEMENT_DELETE) {
                if (slot == null || !(slot.slot() instanceof NormalizedSlot.ArraySlot array)
                        || length == null) {
                    throw new IllegalStateException("an array chain boundary lacks its "
                        + "normalize slot/length facts (a malformed chain — the "
                        + "production protocol rejects this)");
                }
                return BoundaryContext.writeBounds(array.index(),
                    (int) ((Value.IntValue) length).value());
            }
            return BoundaryContext.none();
        }

        /** DELETE: children in payload order; publishes nothing. */
        private String executeDelete(SemanticOp op) {
            KindPayload.DeletePayload payload = (KindPayload.DeletePayload) op.payload();
            for (OpId childId : payload.childOps()) {
                SemanticOp child = opOf(childId);
                completeChainOperands(child);
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    KindPayload.BoundaryPayload boundaryPayload =
                        (KindPayload.BoundaryPayload) child.payload();
                    runBoundaryChild(child, valueOf(boundaryPayload.input()),
                        chainBoundaryContext(op, boundaryPayload.kind()));
                } else {
                    execute(child);
                }
            }
            return null;
        }

        /**
         * A-D2 ("each child's operands complete before that child's
         * START"): the child's transitive operand-producing closure
         * executes at the child's position inside the chain — the
         * receiver/key/RHS operand effects interleave with the children
         * exactly as the hoisted-operand parity fixtures pin (an
         * operand's nested side-effecting argument completes before the
         * operand call's own effect, and the RHS operand effects run
         * only after the key child completed).
         */
        private void completeChainOperands(SemanticOp child) {
            UnitState owner = stateOf(child.opId());
            for (SemanticOp producer : ChainOperandCompletion.operandProducersOf(
                    child, owner.unit, owner.structuralOwned)) {
                execute(producer);
            }
        }

        /**
         * CALL — the D13 machine: parameter boundaries in one-based order
         * with the closed table's cells, then the callee execution per
         * the resolved binding (DIRECT runs the recorded body block;
         * INDIRECT resolves the callee's binding and executes it; HOST
         * performs exactly one host request; EXTERNAL executes the
         * callee unit's EXTERNAL_ENTRY for SHARED_BODY or the target ABI
         * terminal for RETAINED_ABI), then the single return boundary of
         * the shape — by the callee's RETURN for bodies, by the call op
         * for host terminals and retained-ABI externals. A DYNAMIC
         * callee resolves its identity at execution and executes the
         * selected recorded return-boundary cell per the closed runtime
         * resolution protocol ({@link #executeDynamicCall}).
         */
        private String executeCall(SemanticOp op) {
            KindPayload.CallPayload payload = (KindPayload.CallPayload) op.payload();
            List<Value> checkedArgs = runParameterBoundaries(op,
                payload.parameterBoundaryOpIds());
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                case KindPayload.CallCallee.Indirect indirect -> resolveBindingOf(indirect.callee());
                case KindPayload.CallCallee.Dynamic dynamic -> resolveBindingOf(dynamic.callee());
            };
            Value returned = payload.callee() instanceof KindPayload.CallCallee.Dynamic
                ? executeDynamicCall(op, payload, binding, checkedArgs)
                : switch (binding) {
                    case FunctionExecutionBinding.LoweredBody body ->
                        invokeLoweredBody(op, payload, body, checkedArgs);
                    case FunctionExecutionBinding.AdapterBinding adapter ->
                        invokeAdapter(op, payload, adapter, checkedArgs);
                    case FunctionExecutionBinding.HostFunction host ->
                        invokeHostCallWithBoundary(op, payload, host.hostModuleId(),
                            host.exportName(), host.descriptor(), checkedArgs);
                    case FunctionExecutionBinding.HostFunctionValue hostValue ->
                        invokeHostCallWithBoundary(op, payload, hostValue.hostModuleId(),
                            "@value#" + hostValue.materializingBoundaryOpId().id(),
                            hostValue.descriptor(), checkedArgs);
                    case FunctionExecutionBinding.ExternalFunction external ->
                        invokeExternalCall(op, payload, external, checkedArgs);
                    case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                        throw intrinsicExecutionDefect(intrinsic);
                };
            return publish(op, returned);
        }

        /** The parameter boundaries of one call/async/callback op in one-based order. */
        private List<Value> runParameterBoundaries(SemanticOp op, List<OpId> boundaryIds) {
            List<Value> checked = new ArrayList<>();
            for (int i = 0; i < boundaryIds.size(); i++) {
                SemanticOp boundary = opOf(boundaryIds.get(i));
                Value arg = valueOf(
                    ((KindPayload.BoundaryPayload) boundary.payload()).input());
                checked.add(runBoundaryChild(boundary, arg,
                    BoundaryContext.parameter(i + 1)));
            }
            return checked;
        }

        /** The body execution of one LoweredBody binding under the invoking op. */
        private Value invokeLoweredBody(SemanticOp op, KindPayload.CallPayload payload,
                                        FunctionExecutionBinding.LoweredBody body,
                                        List<Value> checkedArgs) {
            UnitState state = stateOf(op.opId());
            LoweredFunction function = state.unit.functions().get(body.functionId());
            if (function == null) {
                throw new IllegalStateException("CALL resolves a missing lowered function "
                    + body.functionId());
            }
            bindParamCells(state, body.blockId(), payload.signature().paramTypes().size(),
                checkedArgs);
            frames.add(0, body.functionId());
            Value returned;
            try {
                returned = runBodyBlock(body.blockId(),
                    payload.signature().paramTypes().size(), state);
            } finally {
                frames.remove(0);
                popParamCells();
            }
            return returned;
        }

        /** Binds one body block's leading parameter ALLOC cells (the invocation overlay). */
        private void bindParamCells(UnitState state, BlockId bodyBlock, int paramCount,
                                    List<Value> args) {
            pushParamCells(state, bodyBlock, paramCount, args);
        }

        /** The D15 adapter invocation protocol (source class statically fixed). */
        private Value invokeAdapter(SemanticOp op, KindPayload.CallPayload payload,
                                    FunctionExecutionBinding.AdapterBinding adapter,
                                    List<Value> checkedArgs) {
            int m = adapter.sourceSignature().paramTypes().size();
            Value sourceValue = loadAdapterSource(op, adapter);
            checkAdapterSourceSignature(op, adapter, sourceValue);
            FunctionExecutionBinding sourceBinding = resolveBindingOfValue(sourceValue);
            List<Value> leading = List.copyOf(checkedArgs.subList(0, m));
            return switch (sourceBinding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    UnitState state = stateOf(op.opId());
                    bindParamCells(state, body.blockId(), m, leading);
                    frames.add(0, body.functionId());
                    try {
                        yield runBodyBlock(body.blockId(), m, state);
                    } finally {
                        frames.remove(0);
                        popParamCells();
                    }
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    Value value = invokeHostRequest(op, host.hostModuleId(),
                        host.exportName(), host.descriptor(), leading);
                    yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                        BoundaryContext.none());
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    Value value = invokeHostRequest(op, hostValue.hostModuleId(),
                        "@value#" + hostValue.materializingBoundaryOpId().id(),
                        hostValue.descriptor(), leading);
                    yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                        BoundaryContext.none());
                }
                case FunctionExecutionBinding.ExternalFunction external -> {
                    if (external.executionOwner() == ExternalExecutionOwner.SHARED_BODY) {
                        yield executeExternalEntryFor(op, payload.externalEntryRef(),
                            external, leading);
                    }
                    Value value = invokeHostRequest(op, external.moduleId(),
                        external.exportName(), external.descriptor(), leading);
                    yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                        BoundaryContext.none());
                }
                case FunctionExecutionBinding.AdapterBinding nested ->
                    throw new IllegalStateException("adapter-of-adapter invocation is "
                        + "outside the statically-resolved slice (ISSUE-0531)");
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicExecutionDefect(intrinsic);
            };
        }

        /**
         * The dynamically resolved CALL terminal (ISSUE-0531): the
         * callee's binding kind was unknown until execution, so the
         * runtime resolves the identity against the registry, classifies
         * the resolution with the closed protocol
         * ({@link DynamicReturnBoundaryProtocol}), and executes the
         * selected recorded return-boundary cell per the closed
         * selection ({@link ReturnBoundarySelection}): the callee's
         * source {@code RETURN} executes the recorded
         * {@code FUNCTION_RETURN} cell for {@code DEAL_BODY}, the call op
         * executes the recorded {@code HOST_TO_DEAL}/
         * {@code EXTERNAL_RETURN} cell for {@code HOST}/{@code EXTERNAL},
         * and {@code SHARED_BODY} executes zero caller-side return
         * boundaries (the callee unit's {@code RETURN} under its
         * {@code EXTERNAL_ENTRY} runs the single {@code EXTERNAL_RETURN}
         * in the callee unit).
         */
        private Value executeDynamicCall(SemanticOp op, KindPayload.CallPayload payload,
                                         FunctionExecutionBinding binding,
                                         List<Value> checkedArgs) {
            if (binding instanceof FunctionExecutionBinding.AdapterBinding adapter) {
                return executeDynamicAdapterCall(op, payload, adapter, checkedArgs);
            }
            DynamicResolutionKind kind = DynamicReturnBoundaryProtocol.kindOf(binding);
            ReturnBoundarySelection selection = DynamicReturnBoundaryProtocol.select(
                payload.dynamicReturnBoundary(), kind);
            return switch (selection) {
                case ReturnBoundarySelection.CalleeReturn ignored ->
                    invokeLoweredBody(op, payload,
                        (FunctionExecutionBinding.LoweredBody) binding, checkedArgs);
                case ReturnBoundarySelection.CallTerminal terminal -> {
                    Value value = invokeResolvedHostRequest(op, binding, checkedArgs);
                    yield runBoundaryChild(opOf(terminal.boundaryOpId()), value,
                        BoundaryContext.none());
                }
                case ReturnBoundarySelection.None ignored -> executeExternalEntryFor(op,
                    externalEntryOpOf((FunctionExecutionBinding.ExternalFunction) binding,
                        false).opId(),
                    (FunctionExecutionBinding.ExternalFunction) binding, checkedArgs);
            };
        }

        /**
         * The dynamically resolved adapter CALL (ISSUE-0531): the D15
         * invocation protocol resolves the adapter's source value and its
         * source binding fixes the resolution class (the adapter carries
         * no source kind of its own —
         * {@link DynamicReturnBoundaryProtocol} fails closed on an
         * adapter input).
         */
        private Value executeDynamicAdapterCall(SemanticOp op,
                KindPayload.CallPayload payload,
                FunctionExecutionBinding.AdapterBinding adapter,
                List<Value> checkedArgs) {
            int m = adapter.sourceSignature().paramTypes().size();
            Value sourceValue = loadAdapterSource(op, adapter);
            checkAdapterSourceSignature(op, adapter, sourceValue);
            FunctionExecutionBinding sourceBinding = resolveBindingOfValue(sourceValue);
            if (sourceBinding instanceof FunctionExecutionBinding.AdapterBinding) {
                throw new IllegalStateException("adapter-of-adapter invocation is "
                    + "outside the statically-resolved slice (ISSUE-0531)");
            }
            DynamicResolutionKind kind = DynamicReturnBoundaryProtocol.kindOf(sourceBinding);
            ReturnBoundarySelection selection = DynamicReturnBoundaryProtocol.select(
                payload.dynamicReturnBoundary(), kind);
            List<Value> leading = List.copyOf(checkedArgs.subList(0, m));
            return switch (selection) {
                case ReturnBoundarySelection.CalleeReturn ignored -> {
                    FunctionExecutionBinding.LoweredBody body =
                        (FunctionExecutionBinding.LoweredBody) sourceBinding;
                    UnitState state = stateOf(op.opId());
                    bindParamCells(state, body.blockId(), m, leading);
                    frames.add(0, body.functionId());
                    try {
                        yield runBodyBlock(body.blockId(), m, state);
                    } finally {
                        frames.remove(0);
                        popParamCells();
                    }
                }
                case ReturnBoundarySelection.CallTerminal terminal -> {
                    Value value = invokeResolvedHostRequest(op, sourceBinding, leading);
                    yield runBoundaryChild(opOf(terminal.boundaryOpId()), value,
                        BoundaryContext.none());
                }
                case ReturnBoundarySelection.None ignored -> executeExternalEntryFor(op,
                    externalEntryOpOf(
                        (FunctionExecutionBinding.ExternalFunction) sourceBinding,
                        false).opId(),
                    (FunctionExecutionBinding.ExternalFunction) sourceBinding, leading);
            };
        }

        /** The host-request terminal of a HOST-class or retained-ABI external binding. */
        private Value invokeResolvedHostRequest(SemanticOp op,
                FunctionExecutionBinding binding, List<Value> args) {
            return switch (binding) {
                case FunctionExecutionBinding.HostFunction host -> invokeHostRequest(op,
                    host.hostModuleId(), host.exportName(), host.descriptor(), args);
                case FunctionExecutionBinding.HostFunctionValue hostValue ->
                    invokeHostRequest(op, hostValue.hostModuleId(),
                        "@value#" + hostValue.materializingBoundaryOpId().id(),
                        hostValue.descriptor(), args);
                case FunctionExecutionBinding.ExternalFunction external ->
                    invokeHostRequest(op, external.moduleId(), external.exportName(),
                        external.descriptor(), args);
                case FunctionExecutionBinding.LoweredBody ignored ->
                    throw new IllegalStateException("a DEAL-body binding never executes "
                        + "a call-terminal return boundary (producer defect)");
                case FunctionExecutionBinding.AdapterBinding ignored ->
                    throw new IllegalStateException("an adapter binding resolves its "
                        + "source before classification (producer defect)");
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicExecutionDefect(intrinsic);
            };
        }

        /** The callee unit's sync/async EXTERNAL_ENTRY for one external binding. */
        private SemanticOp externalEntryOpOf(
                FunctionExecutionBinding.ExternalFunction external, boolean async) {
            UnitState state = units.get(external.moduleId());
            if (state == null) {
                throw new IllegalStateException("the external callee module "
                    + external.moduleId() + " is not in the closure (producer defect)");
            }
            for (SemanticOp op : state.unit.ops()) {
                if (op.kind() == SemanticOpKind.EXTERNAL_ENTRY) {
                    KindPayload.ExternalEntryPayload entryPayload =
                        (KindPayload.ExternalEntryPayload) op.payload();
                    if (entryPayload.async() == async
                            && entryPayload.exportName().equals(external.exportName())) {
                        return op;
                    }
                }
            }
            throw new IllegalStateException("module " + external.moduleId()
                + " records no " + (async ? "async" : "sync")
                + " EXTERNAL_ENTRY for export '" + external.exportName()
                + "' (producer defect)");
        }

        /** The D15 source load: VALUE retains, SHARED_CELL re-reads, THUNK re-executes. */
        private Value loadAdapterSource(SemanticOp op,
                                        FunctionExecutionBinding.AdapterBinding adapter) {
            return switch (adapter.sourceRef()) {
                case AdaptSourceRef.Value value -> valueOf(value.value());
                case AdaptSourceRef.SharedCell cell -> {
                    Cell loaded = cellOf(cell.binding(), cell.generation(), false);
                    if (loaded == null || !loaded.initialized) {
                        throw new IllegalStateException("the adapter's SHARED_CELL load "
                            + "of an uninitialized cell " + cell.binding() + "#"
                            + cell.generation() + " (producer defect)");
                    }
                    yield loaded.value;
                }
                case AdaptSourceRef.Thunk thunk -> runThunkBlock(op, thunk);
            };
        }

        /** The adapter's source-signature check: E8010 FUNCTION_SIGNATURE at the invocation. */
        private void checkAdapterSourceSignature(SemanticOp op,
                FunctionExecutionBinding.AdapterBinding adapter, Value sourceValue) {
            BoundaryOutcome outcome = BoundaryExecutor.check(
                FailurePolicyId.FUNCTION_SIGNATURE, adapter.sourceSignature(),
                viewOfValue(sourceValue), BoundaryContext.none());
            switch (outcome) {
                case BoundaryOutcome.Pass ignored -> { }
                case BoundaryOutcome.Fail fail -> throw DealFailure.of(fail.failure(),
                    op.origin(), List.copyOf(frames));
            }
        }

        /** The REEVALUATE_THUNK source re-execution (side effects repeat per invoke). */
        private Value runThunkBlock(SemanticOp invocation, AdaptSourceRef.Thunk thunk) {
            UnitState state = stateOf(invocation.opId());
            List<OpId> ops = state.table.blockOps().get(thunk.blockId());
            if (ops == null) {
                throw new IllegalStateException("the adapter thunk block "
                    + thunk.blockId() + " has no membership row (producer defect)");
            }
            Value produced = null;
            for (OpId opId : ops) {
                if (state.ownedChildren.contains(opId)) {
                    continue;
                }
                SemanticOp thunkOp = state.opsById.get(opId);
                if (thunkOp == null) {
                    throw new IllegalStateException("op " + opId
                        + " is not a member of the validated unit");
                }
                execute(thunkOp);
                if (thunkOp.result() instanceof ValueId valueId) {
                    produced = valueOf(valueId);
                }
            }
            return produced;
        }

        /** One host request effect with its ordered terminal. */
        private Value invokeHostRequest(SemanticOp op, ModuleId module, String export,
                                        RuntimeDescriptor.Func descriptor, List<Value> args) {
            if (responder == null) {
                throw new IllegalStateException("a host call requires a deterministic "
                    + "host responder (the E7 host seam)");
            }
            effects.add(new SemanticRuntimeModel.EffectEvent(
                SemanticRuntimeModel.EffectEvent.Kind.HOST_CALL,
                module.path() + "." + export));
            HostResponder.SyncOutcome outcome = responder.call(module, export, descriptor,
                List.copyOf(args));
            return switch (outcome) {
                case HostResponder.SyncOutcome.Returned returned -> {
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.HOST_RETURN,
                        module.path() + "." + export + "=" + atomOf(returned.value())));
                    yield returned.value();
                }
                case HostResponder.SyncOutcome.Thrown thrown -> {
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.HOST_THROW,
                        module.path() + "." + export + "!" + thrown.code()));
                    throw new DealFailure(thrown.code(), thrown.message(), op.origin(),
                        null, null, null, List.copyOf(frames));
                }
            };
        }

        /** A host call plus the call-op-run HOST_TO_DEAL+HOST_SYNC_RETURN boundary. */
        private Value invokeHostCallWithBoundary(SemanticOp op, KindPayload.CallPayload payload,
                ModuleId module, String export, RuntimeDescriptor.Func descriptor,
                List<Value> args) {
            Value value = invokeHostRequest(op, module, export, descriptor, args);
            return runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                BoundaryContext.none());
        }

        /** The external-call terminal per the execution owner. */
        private Value invokeExternalCall(SemanticOp op, KindPayload.CallPayload payload,
                FunctionExecutionBinding.ExternalFunction external, List<Value> args) {
            if (external.executionOwner() == ExternalExecutionOwner.SHARED_BODY) {
                return executeExternalEntryFor(op, payload.externalEntryRef(), external,
                    args);
            }
            Value value = invokeHostRequest(op, external.moduleId(), external.exportName(),
                external.descriptor(), args);
            return runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                BoundaryContext.none());
        }

        /** The callee unit's sync EXTERNAL_ENTRY execution under the triggering caller op. */
        private Value executeExternalEntryFor(SemanticOp caller, OpId entryOpId,
                FunctionExecutionBinding.ExternalFunction external, List<Value> args) {
            if (entryOpId == null) {
                throw new IllegalStateException("the SHARED_BODY external call carries no "
                    + "externalEntryRef (producer defect)");
            }
            SemanticOp entry = opOf(entryOpId);
            UnitState state = stateOf(entryOpId);
            KindPayload.ExternalEntryPayload entryPayload =
                (KindPayload.ExternalEntryPayload) entry.payload();
            if (!entryPayload.exportName().equals(external.exportName())) {
                throw new IllegalStateException("the externalEntryRef names export '"
                    + entryPayload.exportName() + "' but the binding names '"
                    + external.exportName() + "' (producer defect)");
            }
            LoweredFunction function = state.unit.functions().get(entryPayload.function());
            if (function == null) {
                throw new IllegalStateException("EXTERNAL_ENTRY resolves a missing "
                    + "lowered function " + entryPayload.function());
            }
            emitStartParented(entry, caller.opId(), List.of());
            try {
                // The entry runs no parameter boundaries: the caller's
                // EXTERNAL_PARAMETER boundaries ran exactly once.
                bindParamCells(state, function.body(),
                    entryPayload.signature().paramTypes().size(), args);
                frames.add(0, entryPayload.function());
                Value returned;
                try {
                    returned = runBodyBlock(function.body(),
                        entryPayload.signature().paramTypes().size(), state);
                } finally {
                    frames.remove(0);
                    popParamCells();
                }
                emitSuccessParented(entry, caller.opId(), atomOf(returned));
                return returned;
            } catch (DealFailure failure) {
                emitFailureParented(entry, caller.opId(), failure);
                throw failure;
            }
        }

        /** The registered binding of one producing allocation identity, or null. */
        private FunctionExecutionBinding bindingOf(ValueId identity) {
            for (UnitState state : units.values()) {
                FunctionExecutionBinding found = state.unit.functionBindings().get(
                    new FunctionAllocationIdentity(identity.id()));
                if (found != null) {
                    return found;
                }
            }
            return null;
        }

        /** The binding of one callee/function ValueId (fail closed when absent). */
        private FunctionExecutionBinding resolveBindingOf(ValueId callee) {
            FunctionExecutionBinding binding = bindingOf(callee);
            if (binding == null) {
                throw new IllegalStateException("function value " + callee
                    + " has no registered FunctionExecutionBinding (producer defect)");
            }
            return binding;
        }

        /** The heap function value's resolved execution binding (fail closed). */
        private FunctionExecutionBinding resolveBindingOfValue(Value value) {
            FunctionExecutionBinding binding = bindingsByValue.get(value);
            if (binding == null) {
                throw new IllegalStateException("function value " + atomOf(value)
                    + " has no registered FunctionExecutionBinding (producer defect)");
            }
            return binding;
        }

        /**
         * The fail-closed producer defect of an intrinsic carrier's
         * execution: this slice registers the closed
         * {@code IntrinsicFunction} binding only — the carrier's
         * materialization and its call execution are the function-typed
         * -value child's, so no produced unit may resolve one at a call
         * site.
         */
        private static IllegalStateException intrinsicExecutionDefect(
                FunctionExecutionBinding.IntrinsicFunction intrinsic) {
            return new IllegalStateException("the '" + intrinsic.kind() + "' intrinsic "
                + "function value has no execution in this slice (the intrinsic carrier "
                + "is the function-typed-value child's — producer defect)");
        }

        /**
         * Runs a callee body block, skipping the leading parameter ALLOCs
         * (already bound); a RETURN transfers the checked value out.
         */
        private Value runBodyBlock(BlockId block, int skipLeading) {
            return runBodyBlock(block, skipLeading, entry);
        }

        private Value runBodyBlock(BlockId block, int skipLeading, UnitState state) {
            List<OpId> ops = state.table.blockOps().get(block);
            if (ops == null) {
                throw new IllegalStateException("block " + block
                    + " has no membership row (a malformed table — the production "
                    + "validator rejects this)");
            }
            int i = 0;
            for (OpId opId : ops) {
                if (i++ < skipLeading) {
                    continue;
                }
                if (state.ownedChildren.contains(opId)) {
                    continue;
                }
                SemanticOp op = state.opsById.get(opId);
                if (op == null) {
                    throw new IllegalStateException("op " + opId
                        + " is not a member of the validated unit");
                }
                try {
                    execute(op);
                } catch (ReturnSignal signal) {
                    return signal.value;
                }
            }
            return Value.NullValue.INSTANCE;
        }

        /**
         * FUNCTION_ADAPT creation (D15): SUCCESS publishes a fresh
         * adapter identity of the target signature; creation evaluates no
         * thunk and reads no binding (VALUE's single operand already
         * completed).
         */
        private String executeFunctionAdapt(SemanticOp op) {
            KindPayload.FunctionAdaptPayload payload =
                (KindPayload.FunctionAdaptPayload) op.payload();
            Value.AdapterValue adapter = new Value.AdapterValue(payload.targetSignature());
            FunctionExecutionBinding binding = resolveBindingOf((ValueId) op.result());
            bindingsByValue.put(adapter, binding);
            return publish(op, adapter);
        }

        /**
         * ASYNC_START — the per-resolution terminal (D13 step 6): the
         * parameter boundaries in one-based order (zero under
         * {@code ELIDED_BY_ADAPTER}), then the source's own terminal —
         * a canonical token plus one body task for a DEAL body; the
         * adapter protocol plus the nested source {@code ASYNC_START}
         * for adapter-over-async; one host request with the
         * {@code AsyncStart} terminal, handle validation as the op's own
         * {@code ASYNC_OPERATION_HANDLE} terminal check, and a canonical
         * token bound to the operation label for an async host function;
         * the callee unit's async {@code EXTERNAL_ENTRY} for an async
         * external (the caller token aliases the callee canonical token
         * through {@code ExternalAsyncLink}). A DYNAMIC callee resolves
         * its identity at execution and executes the effective source's
         * terminal per the closed runtime resolution protocol
         * ({@link #executeDynamicAsyncStart}).
         */
        private String executeAsyncStart(SemanticOp op) {
            KindPayload.AsyncStartPayload payload =
                (KindPayload.AsyncStartPayload) op.payload();
            // Under ELIDED_BY_ADAPTER the leading-M operand values are the
            // source arguments (zero parameter boundaries — the outer
            // adapter's xN checks are the complete set).
            List<Value> checkedArgs;
            if (payload.parameterBoundaryMode() == ParameterBoundaryMode.ELIDED_BY_ADAPTER) {
                checkedArgs = new ArrayList<>();
                for (ValueId operand : op.operands()) {
                    checkedArgs.add(valueOf(operand));
                }
            } else {
                checkedArgs = runParameterBoundaries(op, payload.parameterBoundaryOpIds());
            }
            FunctionExecutionBinding binding = switch (payload.callee()) {
                case KindPayload.CallCallee.Static staticCallee -> staticCallee.binding();
                case KindPayload.CallCallee.Indirect indirect -> resolveBindingOf(indirect.callee());
                case KindPayload.CallCallee.Dynamic dynamic -> resolveBindingOf(dynamic.callee());
            };
            AsyncTokenId token = (AsyncTokenId) op.result();
            if (payload.callee() instanceof KindPayload.CallCallee.Dynamic) {
                executeDynamicAsyncStart(op, binding, checkedArgs, token);
                return tokenAtom(token);
            }
            switch (binding) {
                case FunctionExecutionBinding.LoweredBody body -> {
                    tasks.put(token.tokenId(), new Task(token,
                        () -> runTaskBody(op, body, checkedArgs)));
                    readyQueue.add(token.tokenId());
                }
                case FunctionExecutionBinding.AdapterBinding adapter -> {
                    tasks.put(token.tokenId(), new Task(token,
                        () -> runAdapterOverAsyncTask(op, adapter, checkedArgs)));
                    readyQueue.add(token.tokenId());
                }
                case FunctionExecutionBinding.HostFunction host -> {
                    requireHostResponder();
                    String label = payload.hostOperationLabel();
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP, label));
                    String bound = responder.startAsync(host.hostModuleId(),
                        host.exportName(), host.descriptor(), List.copyOf(checkedArgs),
                        label);
                    if (bound == null) {
                        throw registryFailure(op, FailurePolicyId.ASYNC_OPERATION_HANDLE,
                            "async-operation", "nothing");
                    }
                    hostOperations.put(token.tokenId(), bound);
                    tasks.put(token.tokenId(), new Task(token, null));
                }
                case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                    requireHostResponder();
                    String label = payload.hostOperationLabel();
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP, label));
                    String bound = responder.startAsync(hostValue.hostModuleId(),
                        "@value#" + hostValue.materializingBoundaryOpId().id(),
                        hostValue.descriptor(), List.copyOf(checkedArgs), label);
                    if (bound == null) {
                        throw registryFailure(op, FailurePolicyId.ASYNC_OPERATION_HANDLE,
                            "async-operation", "nothing");
                    }
                    hostOperations.put(token.tokenId(), bound);
                    tasks.put(token.tokenId(), new Task(token, null));
                }
                case FunctionExecutionBinding.ExternalFunction external -> {
                    if (payload.externalAsyncLink() == null) {
                        throw new IllegalStateException("ASYNC_START(EXTERNAL) without "
                            + "its ExternalAsyncLink (producer defect)");
                    }
                    long calleeTokenId =
                        payload.externalAsyncLink().calleeTokenId().tokenId();
                    SemanticOp entry = opOf(new OpId(external.moduleId(), calleeTokenId));
                    executeAsyncEntry(entry, op.opId(), checkedArgs, calleeTokenId);
                }
                case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                    throw intrinsicExecutionDefect(intrinsic);
            }
            return tokenAtom(token);
        }

        /**
         * The dynamically resolved ASYNC_START terminal (ISSUE-0531):
         * the recorded source is {@code DEAL_BODY} (the only resolution
         * whose caller-recorded return boundary executes — the single
         * {@code FUNCTION_RETURN} task cell run by the task body's
         * {@code RETURN}); the runtime derives the effective source from
         * the resolved binding, and HOST/EXTERNAL/adapter-over-async
         * resolutions execute zero caller-side return boundaries with
         * their linkage (operation label, external async entry) bound at
         * execution.
         */
        private void executeDynamicAsyncStart(SemanticOp op,
                FunctionExecutionBinding binding, List<Value> checkedArgs,
                AsyncTokenId token) {
            if (binding instanceof FunctionExecutionBinding.AdapterBinding adapter) {
                executeDynamicAdapterAsyncStart(op, adapter, checkedArgs, token);
                return;
            }
            DynamicResolutionKind kind = DynamicReturnBoundaryProtocol.kindOf(binding);
            switch (kind) {
                case DEAL_BODY -> {
                    FunctionExecutionBinding.LoweredBody body =
                        (FunctionExecutionBinding.LoweredBody) binding;
                    tasks.put(token.tokenId(), new Task(token,
                        () -> runTaskBody(op, body, checkedArgs)));
                    readyQueue.add(token.tokenId());
                }
                case HOST -> {
                    requireHostResponder();
                    ModuleId module;
                    String export;
                    RuntimeDescriptor.Func descriptor;
                    String label;
                    if (binding instanceof FunctionExecutionBinding.HostFunction host) {
                        module = host.hostModuleId();
                        export = host.exportName();
                        descriptor = host.descriptor();
                        label = module.path() + "." + export;
                    } else {
                        FunctionExecutionBinding.HostFunctionValue hostValue =
                            (FunctionExecutionBinding.HostFunctionValue) binding;
                        module = hostValue.hostModuleId();
                        export = "@value#" + hostValue.materializingBoundaryOpId().id();
                        descriptor = hostValue.descriptor();
                        label = module.path() + ".@value";
                    }
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP, label));
                    String bound = responder.startAsync(module, export, descriptor,
                        List.copyOf(checkedArgs), label);
                    if (bound == null) {
                        throw registryFailure(op, FailurePolicyId.ASYNC_OPERATION_HANDLE,
                            "async-operation", "nothing");
                    }
                    hostOperations.put(token.tokenId(), bound);
                    tasks.put(token.tokenId(), new Task(token, null));
                }
                case EXTERNAL, SHARED_BODY -> {
                    FunctionExecutionBinding.ExternalFunction external =
                        (FunctionExecutionBinding.ExternalFunction) binding;
                    SemanticOp entry = externalEntryOpOf(external, true);
                    long calleeTokenId = entry.opId().id();
                    dynamicReferents.put(token.tokenId(), calleeTokenId);
                    executeAsyncEntry(entry, op.opId(), checkedArgs, calleeTokenId);
                }
            }
        }

        /**
         * The dynamically resolved adapter-over-async task (ISSUE-0531):
         * the D15 source resolution fixes the effective source class;
         * the leading M source arguments come from the outer op's checked
         * target-signature arguments, and the effective source's terminal
         * binds at execution (zero caller-side return boundaries outside
         * the DEAL_BODY resolution's recorded task cell).
         */
        private void executeDynamicAdapterAsyncStart(SemanticOp op,
                FunctionExecutionBinding.AdapterBinding adapter,
                List<Value> checkedArgs, AsyncTokenId token) {
            int m = adapter.sourceSignature().paramTypes().size();
            Value sourceValue = loadAdapterSource(op, adapter);
            checkAdapterSourceSignature(op, adapter, sourceValue);
            FunctionExecutionBinding sourceBinding = resolveBindingOfValue(sourceValue);
            if (sourceBinding instanceof FunctionExecutionBinding.AdapterBinding) {
                throw new IllegalStateException("adapter-of-adapter invocation is "
                    + "outside the statically-resolved slice (ISSUE-0531)");
            }
            List<Value> leading = List.copyOf(checkedArgs.subList(0, m));
            DynamicResolutionKind kind = DynamicReturnBoundaryProtocol.kindOf(sourceBinding);
            switch (kind) {
                case DEAL_BODY -> {
                    FunctionExecutionBinding.LoweredBody body =
                        (FunctionExecutionBinding.LoweredBody) sourceBinding;
                    tasks.put(token.tokenId(), new Task(token, () -> {
                        UnitState state = stateOf(op.opId());
                        bindParamCells(state, body.blockId(), m, leading);
                        frames.add(0, body.functionId());
                        try {
                            return runBodyBlock(body.blockId(), m, state);
                        } finally {
                            frames.remove(0);
                            popParamCells();
                        }
                    }));
                    readyQueue.add(token.tokenId());
                }
                case HOST -> {
                    requireHostResponder();
                    ModuleId module;
                    String export;
                    RuntimeDescriptor.Func descriptor;
                    String label;
                    if (sourceBinding instanceof FunctionExecutionBinding.HostFunction host) {
                        module = host.hostModuleId();
                        export = host.exportName();
                        descriptor = host.descriptor();
                        label = module.path() + "." + export;
                    } else {
                        FunctionExecutionBinding.HostFunctionValue hostValue =
                            (FunctionExecutionBinding.HostFunctionValue) sourceBinding;
                        module = hostValue.hostModuleId();
                        export = "@value#" + hostValue.materializingBoundaryOpId().id();
                        descriptor = hostValue.descriptor();
                        label = module.path() + ".@value";
                    }
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.ASYNC_START_OP, label));
                    String bound = responder.startAsync(module, export, descriptor,
                        List.copyOf(leading), label);
                    if (bound == null) {
                        throw registryFailure(op, FailurePolicyId.ASYNC_OPERATION_HANDLE,
                            "async-operation", "nothing");
                    }
                    hostOperations.put(token.tokenId(), bound);
                    tasks.put(token.tokenId(), new Task(token, null));
                }
                case EXTERNAL, SHARED_BODY -> {
                    FunctionExecutionBinding.ExternalFunction external =
                        (FunctionExecutionBinding.ExternalFunction) sourceBinding;
                    SemanticOp entry = externalEntryOpOf(external, true);
                    long calleeTokenId = entry.opId().id();
                    dynamicReferents.put(token.tokenId(), calleeTokenId);
                    executeAsyncEntry(entry, op.opId(), leading, calleeTokenId);
                }
            }
        }

        /** The deterministic host responder guard (fail closed without one). */
        private void requireHostResponder() {
            if (responder == null) {
                throw new IllegalStateException("an async host call requires a "
                    + "deterministic host responder (the E7 host seam)");
            }
        }

        /** One DEAL body task: the body executes exactly once and completes the token. */
        private Value runTaskBody(SemanticOp op, FunctionExecutionBinding.LoweredBody body,
                                  List<Value> args) {
            UnitState state = stateOf(op.opId());
            bindParamCells(state, body.blockId(), args.size(), args);
            frames.add(0, body.functionId());
            try {
                return runBodyBlock(body.blockId(), args.size(), state);
            } finally {
                frames.remove(0);
                popParamCells();
            }
        }

        /**
         * One adapter-over-async task: the adapter protocol steps, then
         * the nested source {@code ASYNC_START} (ELIDED_BY_ADAPTER) with
         * its own per-resolution terminal; the outer alias token
         * completes by delegation through the source token (zero return
         * boundaries of its own).
         */
        private Value runAdapterOverAsyncTask(SemanticOp op,
                FunctionExecutionBinding.AdapterBinding adapter, List<Value> checkedArgs) {
            Value sourceValue = loadAdapterSource(op, adapter);
            checkAdapterSourceSignature(op, adapter, sourceValue);
            SemanticOp nested = nestedAsyncStartOf(op);
            execute(nested);
            return Value.NullValue.INSTANCE;
        }

        /** The nested source ASYNC_START parented to the outer adapter-over-async op. */
        private SemanticOp nestedAsyncStartOf(SemanticOp outer) {
            for (SemanticOp candidate : stateOf(outer.opId()).unit.ops()) {
                if (candidate.kind() == SemanticOpKind.ASYNC_START
                        && outer.opId().equals(candidate.origin().parentOpId())) {
                    return candidate;
                }
            }
            throw new IllegalStateException("the adapter-over-async task has no nested "
                + "source ASYNC_START (producer defect)");
        }

        /** The callee unit's async EXTERNAL_ENTRY under the triggering caller op. */
        private void executeAsyncEntry(SemanticOp entry, OpId callerOpId, List<Value> args,
                                       long canonicalTokenId) {
            KindPayload.ExternalEntryPayload entryPayload =
                (KindPayload.ExternalEntryPayload) entry.payload();
            if (!entryPayload.async()) {
                throw new IllegalStateException("the async external call's entry is not "
                    + "async (producer defect)");
            }
            AsyncTokenId token = new AsyncTokenId.Canonical(canonicalTokenId,
                AsyncTokenOwner.DEAL_BODY_TASK);
            emitStartParented(entry, callerOpId, List.of());
            tasks.put(canonicalTokenId, new Task(token, () -> runEntryTask(entry, args)));
            readyQueue.add(canonicalTokenId);
            emitSuccessParented(entry, callerOpId, tokenAtom(token));
        }

        /** One async entry body task (the callee unit's canonical token task). */
        private Value runEntryTask(SemanticOp entry, List<Value> args) {
            KindPayload.ExternalEntryPayload entryPayload =
                (KindPayload.ExternalEntryPayload) entry.payload();
            UnitState state = stateOf(entry.opId());
            LoweredFunction function = state.unit.functions().get(entryPayload.function());
            if (function == null) {
                throw new IllegalStateException("EXTERNAL_ENTRY resolves a missing "
                    + "lowered function " + entryPayload.function());
            }
            bindParamCells(state, function.body(),
                entryPayload.signature().paramTypes().size(), args);
            frames.add(0, entryPayload.function());
            try {
                return runBodyBlock(function.body(),
                    entryPayload.signature().paramTypes().size(), state);
            } finally {
                frames.remove(0);
                popParamCells();
            }
        }

        /** The deterministic FIFO task drain (no parallel source execution). */
        private void drainReadyTasks() {
            while (!readyQueue.isEmpty()) {
                long tokenId = readyQueue.poll();
                Task task = tasks.get(tokenId);
                if (task == null || task.ran || task.completed) {
                    continue;
                }
                task.ran = true;
                if (task.body == null) {
                    continue; // host operations complete through the responder.
                }
                try {
                    task.value = task.body.get();
                    task.completed = true;
                } catch (DealFailure failure) {
                    task.failure = failure;
                    task.completed = true;
                }
            }
        }

        /**
         * AWAIT — the completion position (D13 step 6): the deterministic
         * FIFO drain first, then the token's completion. Alias tokens
         * complete exactly when their canonical referent completes, with
         * the referent's completion value/error unchanged; a failed
         * operation publishes the identical error (never a re-check or a
         * synthesized copy) and a completed value crosses the single
         * {@code ASYNC_COMPLETION} boundary at the await site. Host
         * operation tokens complete from the host through the responder.
         */
        private String executeAwait(SemanticOp op) {
            KindPayload.AwaitPayload payload = (KindPayload.AwaitPayload) op.payload();
            drainReadyTasks();
            long canonicalId = canonicalReferent(payload.token());
            Task task = tasks.get(canonicalId);
            if (task == null) {
                throw new IllegalStateException("AWAIT consumes an unbound token "
                    + payload.token() + " (producer defect)");
            }
            if (!task.completed) {
                // A host operation: the completion arrives from the host.
                String label = hostOperations.get(canonicalId);
                if (label == null) {
                    throw new IllegalStateException("the AWAIT token " + payload.token()
                        + " has no task and no host operation label (producer defect)");
                }
                requireHostResponder();
                HostResponder.SyncOutcome outcome = responder.completeAsync(label);
                switch (outcome) {
                    case HostResponder.SyncOutcome.Returned returned -> {
                        effects.add(new SemanticRuntimeModel.EffectEvent(
                            SemanticRuntimeModel.EffectEvent.Kind.ASYNC_COMPLETE_RETURN,
                            label + "=" + atomOf(returned.value())));
                        task.value = returned.value();
                        task.completed = true;
                    }
                    case HostResponder.SyncOutcome.Thrown thrown -> {
                        effects.add(new SemanticRuntimeModel.EffectEvent(
                            SemanticRuntimeModel.EffectEvent.Kind.ASYNC_COMPLETE_THROW,
                            label + "!" + thrown.code()));
                        task.failure = new DealFailure(thrown.code(), thrown.message(),
                            op.origin(), null, null, null, List.copyOf(frames));
                        task.completed = true;
                    }
                }
            }
            if (task.failure != null) {
                throw task.failure; // the identical error — never re-checked or copied
            }
            Value completed = task.value == null ? Value.NullValue.INSTANCE : task.value;
            SemanticOp boundary = opOf(payload.completionBoundaryOpId());
            Value checked = runBoundaryChild(boundary, completed, BoundaryContext.none());
            return publish(op, checked);
        }

        /** The canonical referent token identity (alias chains resolve transitively). */
        long canonicalReferent(AsyncTokenId token) {
            AsyncTokenId current = token;
            Set<Long> seen = new HashSet<>();
            while (current instanceof AsyncTokenId.Alias alias) {
                if (!seen.add(current.tokenId())) {
                    throw new IllegalStateException("alias cycle over token " + current);
                }
                current = alias.referent();
            }
            Long dynamicReferent = dynamicReferents.get(current.tokenId());
            return dynamicReferent != null ? dynamicReferent : current.tokenId();
        }

        /**
         * EXPORT_PUBLISH — the atomic publication record: the
         * MODULE_EXPORT boundary (descriptor-kind) checks the published
         * value, then the value is recorded in the per-run export-surface
         * registry (M3: the oracle's mirror of the artifacts'
         * program-scoped registry). A second publication of one name in
         * one run is a producer defect — the registry holds exactly one
         * value per {@code (module, name)} and is never rewritten.
         */
        private String executeExportPublish(SemanticOp op) {
            KindPayload.ExportPublishPayload payload =
                (KindPayload.ExportPublishPayload) op.payload();
            Value value = valueOf(payload.value());
            for (SemanticOp candidate : stateOf(op.opId()).unit.ops()) {
                if (candidate.kind() == SemanticOpKind.BOUNDARY
                        && op.opId().equals(candidate.origin().parentOpId())
                        && ((KindPayload.BoundaryPayload) candidate.payload()).kind()
                            == BoundaryKind.MODULE_EXPORT) {
                    runBoundaryChild(candidate, value, BoundaryContext.none());
                }
            }
            Map<String, Value> surface = exportSurfaces.computeIfAbsent(
                payload.module(), ignored -> new LinkedHashMap<>());
            if (surface.containsKey(payload.name())) {
                throw new IllegalStateException("the export '" + payload.module().path()
                    + "#" + payload.name() + "' is published twice in one run (the"
                    + " per-run export surface records exactly one published value per"
                    + " export — a producer defect)");
            }
            surface.put(payload.name(), value);
            return null;
        }

        /**
         * ENTRY_INVOKE — delegates exactly one {@code CALL(DIRECT)} to
         * {@code main}: null and exits the program after the terminal.
         */
        private String executeEntryInvoke(SemanticOp op) {
            SemanticOp call = entryCallOf(op);
            execute(call);
            entryResultAtom = atomOf(valueOf((ValueId) call.result()));
            return null;
        }

        /** The delegated CALL child parented to the entry op. */
        private SemanticOp entryCallOf(SemanticOp entry) {
            for (SemanticOp candidate : stateOf(entry.opId()).unit.ops()) {
                if (candidate.kind() == SemanticOpKind.CALL
                        && entry.opId().equals(candidate.origin().parentOpId())) {
                    return candidate;
                }
            }
            throw new IllegalStateException("ENTRY_INVOKE without its delegated CALL "
                + "(producer defect)");
        }

        /**
         * The CALLBACK_INVOKE execution (host-driven, top-level): one
         * START event with the scripted argument inputs and no
         * {@code parentOpId} (the scenario {@code InvokeCallback} step
         * triggers it), the {@code HOST_TO_DEAL} parameter boundaries in
         * one-based order, the resolved execution binding, and the single
         * {@code DEAL_TO_HOST} return boundary — by the executed body's
         * {@code RETURN} for bodies and DEAL-body-source adapters, by the
         * callback op for host/external functions and host/external-source
         * adapters — then the op's terminal event (SUCCESS with the
         * checked value, or FAILURE with the propagated error). Sync
         * functions only.
         */
        private Value executeCallback(SemanticOp callback, List<Value> args) {
            KindPayload.CallbackInvokePayload payload =
                (KindPayload.CallbackInvokePayload) callback.payload();
            List<String> inputs = new ArrayList<>();
            for (Value arg : args) {
                inputs.add(atomOf(arg));
            }
            emitStart(callback, inputs);
            try {
                List<Value> checked = new ArrayList<>();
                for (int i = 0; i < payload.parameterBoundaryOpIds().size(); i++) {
                    SemanticOp boundary = opOf(payload.parameterBoundaryOpIds().get(i));
                    Value arg = i < args.size() ? args.get(i)
                        : Value.MissingValue.INSTANCE;
                    putValue(((KindPayload.BoundaryPayload) boundary.payload()).input(),
                        arg);
                    checked.add(runBoundaryChild(boundary, arg,
                        BoundaryContext.parameter(i + 1)));
                }
                FunctionExecutionBinding binding = resolveBindingOf(payload.function());
                Value returned = switch (binding) {
                    case FunctionExecutionBinding.LoweredBody body -> {
                        UnitState state = stateOf(callback.opId());
                        bindParamCells(state, body.blockId(),
                            payload.descriptor().paramTypes().size(), checked);
                        frames.add(0, body.functionId());
                        try {
                            yield runBodyBlock(body.blockId(),
                                payload.descriptor().paramTypes().size(), state);
                        } finally {
                            frames.remove(0);
                            popParamCells();
                        }
                    }
                    case FunctionExecutionBinding.AdapterBinding adapter -> {
                        int m = adapter.sourceSignature().paramTypes().size();
                        Value sourceValue = loadAdapterSource(callback, adapter);
                        checkAdapterSourceSignature(callback, adapter, sourceValue);
                        FunctionExecutionBinding sourceBinding =
                            resolveBindingOfValue(sourceValue);
                        List<Value> leading = List.copyOf(checked.subList(0, m));
                        yield switch (sourceBinding) {
                            case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                                throw intrinsicExecutionDefect(intrinsic);
                            case FunctionExecutionBinding.LoweredBody body -> {
                                UnitState state = stateOf(callback.opId());
                                bindParamCells(state, body.blockId(), m, leading);
                                frames.add(0, body.functionId());
                                try {
                                    yield runBodyBlock(body.blockId(), m, state);
                                } finally {
                                    frames.remove(0);
                                    popParamCells();
                                }
                            }
                            case FunctionExecutionBinding.HostFunction host -> {
                                Value value = invokeHostRequest(callback,
                                    host.hostModuleId(), host.exportName(),
                                    host.descriptor(), leading);
                                yield runBoundaryChild(opOf(payload.returnBoundaryOpId()),
                                    value, BoundaryContext.none());
                            }
                            case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                                Value value = invokeHostRequest(callback,
                                    hostValue.hostModuleId(),
                                    "@value#" + hostValue.materializingBoundaryOpId().id(),
                                    hostValue.descriptor(), leading);
                                yield runBoundaryChild(opOf(payload.returnBoundaryOpId()),
                                    value, BoundaryContext.none());
                            }
                            case FunctionExecutionBinding.ExternalFunction external -> {
                                Value value = invokeHostRequest(callback,
                                    external.moduleId(), external.exportName(),
                                    external.descriptor(), leading);
                                yield runBoundaryChild(opOf(payload.returnBoundaryOpId()),
                                    value, BoundaryContext.none());
                            }
                            case FunctionExecutionBinding.AdapterBinding nested ->
                                throw new IllegalStateException("adapter-of-adapter "
                                    + "invocation is outside the statically-resolved "
                                    + "slice (ISSUE-0531)");
                        };
                    }
                    case FunctionExecutionBinding.HostFunction host -> {
                        Value value = invokeHostRequest(callback, host.hostModuleId(),
                            host.exportName(), host.descriptor(), checked);
                        yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                            BoundaryContext.none());
                    }
                    case FunctionExecutionBinding.HostFunctionValue hostValue -> {
                        Value value = invokeHostRequest(callback, hostValue.hostModuleId(),
                            "@value#" + hostValue.materializingBoundaryOpId().id(),
                            hostValue.descriptor(), checked);
                        yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                            BoundaryContext.none());
                    }
                    case FunctionExecutionBinding.ExternalFunction external -> {
                        Value value = invokeHostRequest(callback, external.moduleId(),
                            external.exportName(), external.descriptor(), checked);
                        yield runBoundaryChild(opOf(payload.returnBoundaryOpId()), value,
                            BoundaryContext.none());
                    }
                    case FunctionExecutionBinding.IntrinsicFunction intrinsic ->
                        throw intrinsicExecutionDefect(intrinsic);
                };
                emitSuccess(callback, atomOf(returned));
                return returned;
            } catch (DealFailure failure) {
                emitFailure(callback, failure);
                throw failure;
            }
        }

        private String executeIntrinsic(SemanticOp op) {
            KindPayload.IntrinsicCallPayload payload =
                (KindPayload.IntrinsicCallPayload) op.payload();
            Value input = valueOf(payload.input());
            Value result = switch (payload.kind()) {
                case INT_CONVERT -> convertInt(op, input);
                case NUMBER_CONVERT -> convertNumber(op, input);
            };
            return publish(op, result);
        }

        /** INT_CONVERSION order: null → NaN → infinity → fractional → E8004. */
        private Value convertInt(SemanticOp op, Value input) {
            if (input instanceof Value.NullValue) {
                throw conversionFailure(op, FailurePolicyId.INT_CONVERSION, "int",
                    "null", null);
            }
            if (input instanceof Value.NumValue num) {
                double value = num.value();
                if (Double.isNaN(value)) {
                    throw conversionFailure(op, FailurePolicyId.INT_CONVERSION, "int",
                        "NaN", null);
                }
                if (Double.isInfinite(value)) {
                    throw conversionFailure(op, FailurePolicyId.INT_CONVERSION, "int",
                        "infinity", null);
                }
                if (value != Math.rint(value)) {
                    throw conversionFailure(op, FailurePolicyId.INT_CONVERSION, "int",
                        "non-integer number", null);
                }
                if (value < -2147483648d || value > 2147483647d) {
                    throw conversionFailure(op, FailurePolicyId.INT32_RESULT, "int",
                        null, null);
                }
                return new Value.IntValue((long) value);
            }
            if (input instanceof Value.IntValue intValue) {
                return intValue;
            }
            throw conversionFailure(op, FailurePolicyId.INT_CONVERSION, "int",
                canonicalKind(input), null);
        }

        private Value convertNumber(SemanticOp op, Value input) {
            if (input instanceof Value.NullValue) {
                throw conversionFailure(op, FailurePolicyId.NUMBER_CONVERSION, "number",
                    "null", null);
            }
            if (input instanceof Value.IntValue intValue) {
                return new Value.NumValue((double) intValue.value());
            }
            if (input instanceof Value.NumValue num) {
                return num;
            }
            throw conversionFailure(op, FailurePolicyId.NUMBER_CONVERSION, "number",
                canonicalKind(input), null);
        }

        /** The canonical actual-kind token of a runtime value. */
        private String canonicalKind(Value input) {
            return switch (input) {
                case Value.NullValue ignored -> "null";
                case Value.BoolValue ignored -> "boolean";
                case Value.IntValue ignored -> "int";
                case Value.NumValue ignored -> "number";
                case Value.StrValue ignored -> "string";
                case Value.TableValue ignored -> "table";
                case Value.ArrayValue ignored -> "array";
                case Value.FuncValue ignored -> "function";
                case Value.AdapterValue ignored -> "function";
                case Value.IntrinsicValue ignored -> "function";
                case Value.StdlibCallableValue ignored -> "function";
                case Value.ErrorValue ignored -> "class:@builtin/Error";
                case Value.ClassValue classValue -> "class:" + classValue.classId().text();
                case Value.MissingValue ignored -> "missing";
                case Value.SlotValue ignored -> throw new IllegalStateException(
                    "a slot value is never a conversion input");
            };
        }

        private DealFailure conversionFailure(SemanticOp op, FailurePolicyId policy,
                                              String expected, String actual,
                                              String messageOverride) {
            if (messageOverride == null) {
                BoundaryFailure failure = BoundaryFailure.fromRow(
                    FailureContractRegistry.row(policy), 0, expected, actual,
                    new LinkedHashMap<>(), null);
                return DealFailure.of(failure, op.origin(), List.copyOf(frames));
            }
            return new DealFailure("E8001", messageOverride, op.origin(), expected, actual,
                null, List.copyOf(frames));
        }

        private String executeStdlib(SemanticOp op) {
            KindPayload.StdlibCallPayload payload =
                (KindPayload.StdlibCallPayload) op.payload();
            // Step 1 — precedence (parent D13 step 3 / closed
            // STDLIB_CALL cell): every STDLIB_PARAMETER boundary runs in
            // one-based order before any algorithm executes; the first
            // failing parameter boundary wins (descriptor-kind rule,
            // including E8001 "expected string, got invalid Unicode
            // scalar encoding" at the boundary origin).
            List<Value> checked = new ArrayList<>();
            for (int i = 0; i < payload.args().size(); i++) {
                Value value = valueOf(payload.args().get(i));
                SemanticOp boundary = parameterBoundaryOf(op, i);
                if (boundary != null) {
                    value = runBoundaryChild(boundary, value,
                        BoundaryContext.parameter(i + 1));
                }
                checked.add(value);
            }
            // Step 2 — the shared algorithm: SharedStdlibSemantics is the
            // single executor of the 21 named operations
            // (stdlib-operations-and-time-lock D4 plus the K7 std.time
            // row) over the boundary-admitted carriers; a failure is the
            // primitive's registry-row projection resolved with the row's
            // pinned origin (the STDLIB_CALL call origin) and the active
            // DEAL frames.
            List<SharedStdlibSemantics.Value> argv = new ArrayList<>();
            for (Value value : checked) {
                argv.add(stdlibCarrierOf(value));
            }
            SharedStdlibSemantics.ConsoleSink sink = consoleSinkFor(payload.function());
            SharedStdlibSemantics.Outcome<SharedStdlibSemantics.Value> outcome =
                SharedStdlibSemantics.execute(op, argv, sink, ORACLE_CLOCK);
            return switch (outcome) {
                case SharedStdlibSemantics.Outcome.Success<SharedStdlibSemantics.Value>
                        success -> {
                    Value result = stdlibResultOf(success.value());
                    // Step 3 — the single STDLIB_RETURN boundary run by
                    // the call op after the algorithm result
                    // (descriptor-kind rule); a successful parse whose
                    // top-level value is not a table fails here.
                    SemanticOp returnBoundary = returnBoundaryOf(op);
                    if (returnBoundary != null) {
                        result = runBoundaryChild(returnBoundary, result,
                            BoundaryContext.none());
                    }
                    yield publish(op, result);
                }
                case SharedStdlibSemantics.Outcome.Failure<SharedStdlibSemantics.Value>
                        failure -> {
                    SharedStdlibSemantics.StdlibFailure stdlibFailure = failure.failure();
                    throw DealFailure.of(stdlibFailure.failure(), stdlibFailure.origin(),
                        List.copyOf(frames));
                }
            };
        }

        /** The STDLIB_PARAMETER child for the i-th argument, or null. */
        private SemanticOp parameterBoundaryOf(SemanticOp op, int index) {
            List<SemanticOp> children = stateOf(op.opId()).childrenByParent.get(op.opId());
            if (children == null) {
                return null;
            }
            int seen = 0;
            for (SemanticOp child : children) {
                if (child.kind() == SemanticOpKind.BOUNDARY) {
                    KindPayload.BoundaryPayload payload =
                        (KindPayload.BoundaryPayload) child.payload();
                    if (payload.kind() == deal.semantic.ir.BoundaryKind.STDLIB_PARAMETER) {
                        if (seen == index) {
                            return child;
                        }
                        seen++;
                    }
                }
            }
            return null;
        }

        // =========================================================================
        // Stdlib carrier conversion (oracle value model <-> SharedStdlibSemantics)
        // =========================================================================

        /**
         * The oracle runtime value → the closed stdlib carrier
         * ({@link SharedStdlibSemantics.Value}): the same closed value
         * view the oracle heap realizes, converted recursively for table
         * and array members (JSON data shapes). Values outside the
         * boundary-admitted set fail closed — the parameter boundaries
         * already passed, so such a carrier is a producer defect, never
         * a DEAL projection.
         */
        private SharedStdlibSemantics.Value stdlibCarrierOf(Value value) {
            return switch (value) {
                case Value.NullValue ignored ->
                    SharedStdlibSemantics.Value.Null.INSTANCE;
                case Value.BoolValue bool ->
                    new SharedStdlibSemantics.Value.Bool(bool.value());
                case Value.IntValue intValue -> {
                    long v = intValue.value();
                    if (v < Integer.MIN_VALUE || v > Integer.MAX_VALUE) {
                        throw new IllegalStateException(
                            "a stdlib int carrier must be signed32; got " + v
                                + " (the int parameter boundary's admission set)");
                    }
                    yield new SharedStdlibSemantics.Value.Int((int) v);
                }
                case Value.NumValue num ->
                    new SharedStdlibSemantics.Value.Number(num.value());
                case Value.StrValue str ->
                    SharedStdlibSemantics.Value.string(str.value());
                case Value.TableValue table -> new SharedStdlibSemantics.Value.Table(
                    stdlibTableCarrierOf(table));
                case Value.ArrayValue array -> stdlibArrayCarrierOf(array);
                case Value.FuncValue ignored ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.FUNCTION, null);
                case Value.AdapterValue ignored ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.FUNCTION, null);
                case Value.IntrinsicValue ignored ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.FUNCTION, null);
                case Value.StdlibCallableValue ignored ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.FUNCTION, null);
                case Value.ErrorValue ignored -> new SharedStdlibSemantics.Value.Other(
                    ActualKind.CLASS, "@builtin/Error");
                case Value.ClassValue classValue ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.CLASS,
                        classValue.classId().text());
                case Value.MissingValue ignored ->
                    new SharedStdlibSemantics.Value.Other(ActualKind.MISSING, null);
                case Value.SlotValue ignored -> throw new IllegalStateException(
                    "a slot value is never a stdlib argument carrier");
            };
        }

        /** One oracle table → the closed stdlib table carrier (first-insertion order). */
        private SemanticTable<SharedStdlibSemantics.Value> stdlibTableCarrierOf(
                Value.TableValue table) {
            SemanticTable<SharedStdlibSemantics.Value> carrier = new SemanticTable<>();
            for (Map.Entry<String, Value> entry : table.entries().entrySet()) {
                carrier.put(entry.getKey(), stdlibCarrierOf(entry.getValue()));
            }
            return carrier;
        }

        /** One oracle array → the closed stdlib array carrier (index order). */
        private SharedStdlibSemantics.Value.Array stdlibArrayCarrierOf(
                Value.ArrayValue array) {
            List<SharedStdlibSemantics.Value> elements = new ArrayList<>();
            for (Value element : array.elements()) {
                elements.add(stdlibCarrierOf(element));
            }
            return (SharedStdlibSemantics.Value.Array)
                SharedStdlibSemantics.Value.array(elements);
        }

        /**
         * The shared algorithm result → the oracle runtime value
         * (recursive for the JSON data shapes the stringify/parse
         * algorithms publish: null/boolean/int/number/string leaves,
         * first-insertion-order tables, index-order arrays).
         */
        private Value stdlibResultOf(SharedStdlibSemantics.Value value) {
            return switch (value) {
                case SharedStdlibSemantics.Value.Null ignored ->
                    Value.NullValue.INSTANCE;
                case SharedStdlibSemantics.Value.Bool bool ->
                    new Value.BoolValue(bool.value());
                case SharedStdlibSemantics.Value.Int intValue ->
                    new Value.IntValue(intValue.value());
                case SharedStdlibSemantics.Value.Number number ->
                    new Value.NumValue(number.value());
                case SharedStdlibSemantics.Value.String string -> {
                    if (!(string.scalar() instanceof UnicodeScalars.Valid valid)) {
                        throw new IllegalStateException(
                            "a stdlib string result is always scalar-valid");
                    }
                    yield new Value.StrValue(valid.carrier());
                }
                case SharedStdlibSemantics.Value.Table table ->
                    stdlibResultTableOf(table.table());
                case SharedStdlibSemantics.Value.Array array ->
                    stdlibResultArrayOf(array.elements());
                case SharedStdlibSemantics.Value.Other other ->
                    throw new IllegalStateException(
                        "a stdlib algorithm result never carries an unsupported value: "
                            + other.kind());
            };
        }

        /** One closed stdlib table → the oracle table value (first-insertion order). */
        private Value.TableValue stdlibResultTableOf(
                SemanticTable<SharedStdlibSemantics.Value> table) {
            LinkedHashMap<String, Value> entries = new LinkedHashMap<>();
            for (String key : table.keys()) {
                SemanticTable.Lookup<SharedStdlibSemantics.Value> lookup = table.get(key);
                if (!(lookup
                        instanceof SemanticTable.Lookup.Present<SharedStdlibSemantics.Value>
                        present)) {
                    throw new IllegalStateException(
                        "a table key returned by keys() is always present");
                }
                entries.put(key, stdlibResultOf(present.value()));
            }
            return new Value.TableValue(entries);
        }

        /** One closed stdlib array → the oracle array value (index order). */
        private Value.ArrayValue stdlibResultArrayOf(
                SemanticArray<SharedStdlibSemantics.Value> elements) {
            List<Value> result = new ArrayList<>();
            for (int i = 0; i < elements.size(); i++) {
                result.add(stdlibResultOf(elements.elementAt(i)));
            }
            return new Value.ArrayValue(result, JSON_CARRIER_ELEMENT_DESCRIPTOR);
        }

        /**
         * The element descriptor of a JSON-parsed array carrier: untyped
         * JSON data has no declared element descriptor in the closed set,
         * and the field is never consulted on the stdlib result path (the
         * STDLIB_RETURN boundary checks only the declared top-level
         * descriptor). The value only completes the oracle array record.
         */
        private static final RuntimeDescriptor JSON_CARRIER_ELEMENT_DESCRIPTOR =
            new RuntimeDescriptor.Nullable(RuntimeDescriptor.Table.INSTANCE);

        /**
         * The injected console sink of a {@code CONSOLE_LOG}/
         * {@code CONSOLE_ERROR} call (D5), or null for every other id:
         * {@code write} receives the argument's exact scalar UTF-8 bytes
         * plus one ordered {@code \n}, and the oracle records one
         * ordered effect — the protocol effect text is the scalar text
         * (the shared emitters' {@code F|CONSOLE_WRITE} convention; the
         * ordered newline is the byte-level contract's, not part of the
         * recorded text). A sink failure is infrastructure
         * ({@code INFRASTRUCTURE_ONLY}): the primitive never converts it
         * to a DEAL failure and the exception propagates.
         */
        private SharedStdlibSemantics.ConsoleSink consoleSinkFor(
                StdlibFunctionId function) {
            if (function != StdlibFunctionId.CONSOLE_LOG
                    && function != StdlibFunctionId.CONSOLE_ERROR) {
                return null;
            }
            SharedStdlibSemantics.Channel channel =
                function == StdlibFunctionId.CONSOLE_LOG
                    ? SharedStdlibSemantics.Channel.STDOUT
                    : SharedStdlibSemantics.Channel.STDERR;
            return new SharedStdlibSemantics.ConsoleSink() {
                @Override
                public SharedStdlibSemantics.Channel channel() {
                    return channel;
                }

                @Override
                public void write(byte[] bytes) {
                    String text = new String(bytes, 0, bytes.length - 1,
                        StandardCharsets.UTF_8);
                    effects.add(new SemanticRuntimeModel.EffectEvent(
                        SemanticRuntimeModel.EffectEvent.Kind.CONSOLE_WRITE, channel,
                        text));
                }
            };
        }

        /**
         * The injected deterministic clock reading of the oracle
         * ({@code TIME_NOW_MILLIS}, K7 item 4): the oracle never reads
         * the host clock, so its trace stays deterministic. The pinned
         * reading is a contemporary epoch-millisecond value (outside the
         * signed32 range), so the declared {@code int} return boundary
         * fails with the same pinned E8004 projection the real targets
         * produce for their own clock readings.
         */
        private static final long ORACLE_CLOCK_MILLIS = 1_700_000_000_000L;

        /** The oracle's injected clock seam (one constant, never the host clock). */
        private static final SharedStdlibSemantics.Clock ORACLE_CLOCK =
            () -> ORACLE_CLOCK_MILLIS;

        /** The STDLIB_RETURN child, or null. */
        private SemanticOp returnBoundaryOf(SemanticOp op) {
            List<SemanticOp> children = stateOf(op.opId()).childrenByParent.get(op.opId());
            if (children == null) {
                return null;
            }
            for (SemanticOp child : children) {
                if (child.kind() == SemanticOpKind.BOUNDARY
                        && ((KindPayload.BoundaryPayload) child.payload()).kind()
                            == deal.semantic.ir.BoundaryKind.STDLIB_RETURN) {
                    return child;
                }
            }
            return null;
        }

        private String executeBranch(SemanticOp op) {
            KindPayload.BranchPayload payload = (KindPayload.BranchPayload) op.payload();
            Value condition = valueOf(payload.condition());
            boolean truthy = ((Value.BoolValue) condition).value();
            switch (payload.selector()) {
                case IF -> {
                    if (truthy) {
                        runBlock(payload.selectedBlock());
                    } else if (payload.alternateBlock() != null) {
                        runBlock(payload.alternateBlock());
                    }
                    return null;
                }
                case LOGICAL_AND -> {
                    // The right operand's producing ops live in
                    // selectedBlock and execute only when the left value
                    // does not decide the result; the producer wires the
                    // op's result slot to the right operand's value
                    // identity, so the block run publishes it, and a
                    // skipped block publishes the left value.
                    if (!truthy) {
                        return publish(op, condition);
                    }
                    runBlock(payload.selectedBlock());
                    return publish(op, valueOf((ValueId) op.result()));
                }
                case LOGICAL_OR -> {
                    if (truthy) {
                        return publish(op, condition);
                    }
                    runBlock(payload.selectedBlock());
                    return publish(op, valueOf((ValueId) op.result()));
                }
                default -> throw new IllegalStateException("BRANCH selector "
                    + payload.selector());
            }
        }

        private String executeLoop(SemanticOp op) {
            KindPayload.LoopPayload payload = (KindPayload.LoopPayload) op.payload();
            switch (payload.selector()) {
                case WHILE -> {
                    while (true) {
                        runBlock(payload.initBlock());
                        if (!((Value.BoolValue) valueOf(payload.condition())).value()) {
                            break;
                        }
                        try {
                            runBlock(payload.bodyBlock());
                        } catch (LoopSignal signal) {
                            if (!signal.target.equals(op.opId())) {
                                throw signal;
                            }
                            if (!signal.isContinue) {
                                break; // BREAK targeting this loop exits it
                            }
                            // WHILE continue → condition block re-run (top).
                        }
                    }
                    return null;
                }
                case FOR -> {
                    runBlock(payload.initBlock());
                    while (true) {
                        if (!((Value.BoolValue) valueOf(payload.condition())).value()) {
                            break;
                        }
                        boolean broken = false;
                        try {
                            runBlock(payload.bodyBlock());
                        } catch (LoopSignal signal) {
                            if (!signal.target.equals(op.opId())) {
                                throw signal;
                            }
                            if (!signal.isContinue) {
                                break;
                            }
                            // FOR continue → update, then re-test.
                        }
                        if (broken) {
                            break;
                        }
                        if (payload.updateBlock() != null) {
                            try {
                                runBlock(payload.updateBlock());
                            } catch (LoopSignal signal) {
                                if (!signal.target.equals(op.opId())) {
                                    throw signal;
                                }
                                if (!signal.isContinue) {
                                    break;
                                }
                            }
                        }
                    }
                    return null;
                }
                default -> throw new IllegalStateException("LOOP selector " + payload.selector());
            }
        }

        private String executeForEach(SemanticOp op) {
            KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) op.payload();
            Value iterable = valueOf(payload.iterable());
            switch (payload.mode()) {
                case ARRAY_VALUES -> {
                    Value.ArrayValue array = (Value.ArrayValue) iterable;
                    int initialLength = array.elements().size();
                    RuntimeDescriptor elementDescriptor = elementDescriptorOf(op);
                    for (int i = 0; i < initialLength; i++) {
                        Value element = i < array.elements().size()
                            ? array.elements().get(i) : Value.MissingValue.INSTANCE;
                        // The op's own terminal check: TYPE_DESCRIPTOR over the
                        // element descriptor (a missing element fails E8001
                        // at the FOR_EACH origin before the body runs).
                        Value checked = checkForEachElement(op, element, elementDescriptor);
                        // Fresh binding per iteration.
                        Cell cell = cellOf(payload.binding(), payload.generation(), true);
                        cell.value = checked;
                        cell.initialized = true;
                        try {
                            runBlock(payload.body());
                        } catch (LoopSignal signal) {
                            if (signal.target.equals(op.opId())) {
                                if (!signal.isContinue) {
                                    break;
                                }
                                // continue → next slot index.
                            } else {
                                throw signal;
                            }
                        }
                    }
                    return null;
                }
                case STRING_SCALARS -> {
                    Value.StrValue string = (Value.StrValue) iterable;
                    int[] scalars = string.value().codePoints().toArray();
                    for (int scalar : scalars) {
                        String single = new String(Character.toChars(scalar));
                        Cell cell = cellOf(payload.binding(), payload.generation(), true);
                        cell.value = new Value.StrValue(single);
                        cell.initialized = true;
                        try {
                            runBlock(payload.body());
                        } catch (LoopSignal signal) {
                            if (signal.target.equals(op.opId())) {
                                if (!signal.isContinue) {
                                    break;
                                }
                            } else {
                                throw signal;
                            }
                        }
                    }
                    return null;
                }
            }
            return null;
        }

        /** The FOR_EACH element descriptor: the iterable producer's array element. */
        private RuntimeDescriptor elementDescriptorOf(SemanticOp op) {
            KindPayload.ForEachPayload payload = (KindPayload.ForEachPayload) op.payload();
            for (SemanticOp producer : opsById.values()) {
                if (payload.iterable().equals(producer.result())) {
                    if (producer.resultType() instanceof RuntimeDescriptor.Array array) {
                        return array.element();
                    }
                    return producer.resultType() instanceof RuntimeDescriptor descriptor
                        ? descriptor : RuntimeDescriptor.String.INSTANCE;
                }
            }
            throw new IllegalStateException("FOR_EACH(ARRAY_VALUES) iterable producer is "
                + "absent from the validated unit");
        }

        /** The FOR_EACH op's own TYPE_DESCRIPTOR terminal check (C-D5). */
        private Value checkForEachElement(SemanticOp op, Value element,
                                          RuntimeDescriptor descriptor) {
            BoundaryValueView view = viewOfValue(element);
            BoundaryOutcome outcome = BoundaryExecutor.check(FailurePolicyId.TYPE_DESCRIPTOR,
                descriptor, view, BoundaryContext.none());
            return switch (outcome) {
                case BoundaryOutcome.Pass pass -> valueOfView(pass.value(), element);
                case BoundaryOutcome.Fail fail ->
                    throw DealFailure.of(fail.failure(), op.origin(), List.copyOf(frames));
            };
        }

        private String executeTryCatch(SemanticOp op) {
            KindPayload.TryCatchPayload payload = (KindPayload.TryCatchPayload) op.payload();
            DealFailure caught;
            try {
                runBlock(payload.tryBlock());
                return null; // success: catch skipped
            } catch (DealFailure failure) {
                caught = failure;
            }
            // Reify the DEAL failure as an Error value bound to the catch binding.
            Value.ErrorValue error = new Value.ErrorValue(caught.code, caught.message);
            Cell cell = cellOf(payload.catchBinding(), 0, true);
            cell.value = error;
            cell.initialized = true;
            try {
                runBlock(payload.catchBlock());
            } catch (DealFailure replacement) {
                throw new DealFailure(replacement.code, replacement.message,
                    replacement.origin, replacement.expected, replacement.actual,
                    caught, replacement.frames);
            }
            return null;
        }

        private String executeThrow(SemanticOp op) {
            KindPayload.ThrowPayload payload = (KindPayload.ThrowPayload) op.payload();
            Value.ErrorValue error = (Value.ErrorValue) valueOf(payload.errorValue());
            throw new DealFailure(error.code(), error.message(), op.origin(), null, null,
                null, List.copyOf(frames));
        }

        private String executeReturn(SemanticOp op) {
            KindPayload.ReturnPayload payload = (KindPayload.ReturnPayload) op.payload();
            Value value = payload.value() == null
                ? Value.NullValue.INSTANCE : valueOf(payload.value());
            SemanticOp boundary = opOf(payload.returnBoundaryOpId());
            Value checked = runBoundaryChild(boundary, value, BoundaryContext.none());
            throw new ReturnSignal(checked);
        }

        private String executeBreak(SemanticOp op) {
            KindPayload.BreakPayload payload = (KindPayload.BreakPayload) op.payload();
            throw new LoopSignal(payload.loopId(), false);
        }

        private String executeContinue(SemanticOp op) {
            KindPayload.ContinuePayload payload = (KindPayload.ContinuePayload) op.payload();
            throw new LoopSignal(payload.loopId(), true);
        }

        /**
         * EXPORT_READ — the per-kind read resolution (M3/M4/M5): a COMPILED
         * read publishes the value the owning module's {@code
         * EXPORT_PUBLISH} recorded into the per-run export-surface
         * registry; a HOST/FFI read publishes that registry's entry for the
         * export — for a HOST module the surface is the loaded module table
         * (the entry the calls child's host load surface and the FFI child's
         * {@code load_ffi} surface record under the module identity), so the
         * read re-wraps nothing and runs no host code; an absent surface or
         * entry publishes {@link Value.MissingValue} in both cases (the
         * landed partial-drive parity state, a state a full execution never
         * reaches because a dependency's publication — or its load — runs
         * before any dependent's read). A STDLIB read publishes the closed
         * catalog row's memoized callable ({@link Value.StdlibCallableValue};
         * see {@link #stdlibCallableOf}) — the same catalog entry and the
         * same algorithm authority the direct {@code STDLIB_CALL} arm uses,
         * never a host responder. A read whose unit records no import fact
         * for its module — the test-only class-core carrier sessions, whose
         * units carry no module-level import op — keeps the landed
         * placeholder; every production and conformance session records the
         * resolved import facts, so a read is never guessed from a path.
         *
         * <p>The read does not write the value-keyed binding map
         * (K11/M3): the published value already carries the owner's
         * registration, so re-keying it would replace the owner-side
         * {@code LoweredBody} resolution; a STDLIB read's own created
         * callable is keyed once at its creation and never re-keyed; the
         * read's own registration stays addressable by the read result's
         * allocation identity ({@link #bindingOf}).</p>
         */
        private String executeExportRead(SemanticOp op) {
            KindPayload.ExportReadPayload payload =
                (KindPayload.ExportReadPayload) op.payload();
            ModuleImportKind kind = importKindOf(stateOf(op.opId()), payload.module());
            Value value;
            switch (kind) {
                case COMPILED, HOST -> {
                    Map<String, Value> surface = exportSurfaces.get(payload.module());
                    Value entry = surface == null ? null : surface.get(payload.name());
                    value = entry == null ? Value.MissingValue.INSTANCE : entry;
                }
                case STDLIB -> value = stdlibCallableOf(op, payload);
                case null -> value = new Value.IntrinsicValue("export:"
                    + payload.module().path() + "." + payload.name());
            }
            return publish(op, value);
        }

        /**
         * The cataloged callable of one STDLIB export read (M3/M4): the
         * closed {@link StdlibFunctionCatalog} is the resolution authority —
         * the read's checked descriptor must be the row's declared
         * descriptor, and an out-of-catalog member or a descriptor mismatch
         * is a fail-closed producer defect (the lowering guards reject both,
         * so a produced unit never reaches this arm). The callable is
         * memoized once per run per {@code (module, name)}: two reads of one
         * cataloged export publish the identical value, and the read's own
         * registration keys that value exactly once at its creation — a
         * later read never re-keys the value-keyed map (a differing existing
         * binding is a producer defect, never a silent overwrite).
         */
        private Value stdlibCallableOf(SemanticOp op, KindPayload.ExportReadPayload payload) {
            StdlibFunctionCatalog.Entry row = StdlibFunctionCatalog
                .lookup(payload.module().path(), payload.name())
                .orElseThrow(() -> new IllegalStateException("the STDLIB export read '"
                    + payload.module().path() + "#" + payload.name() + "' resolves no"
                    + " closed catalog row (the catalog is the STDLIB kind's"
                    + " resolution authority — a producer defect)"));
            if (!(payload.descriptor() instanceof RuntimeDescriptor.Func descriptor)
                    || !row.declaredDescriptor().equals(descriptor)) {
                throw new IllegalStateException("the STDLIB export read '"
                    + payload.module().path() + "#" + payload.name() + "' carries "
                    + payload.descriptor().canonicalSpecText() + " but the closed catalog"
                    + " row declares " + row.declaredDescriptor().canonicalSpecText()
                    + " (the row's declared descriptor is the read's own — a producer"
                    + " defect)");
            }
            String key = payload.module().path() + '\u0001' + payload.name();
            Value.StdlibCallableValue callable = stdlibCallables.get(key);
            FunctionExecutionBinding readBinding = op.result() instanceof ValueId valueId
                ? bindingOf(valueId) : null;
            if (callable == null) {
                callable = new Value.StdlibCallableValue(row.function(), descriptor);
                stdlibCallables.put(key, callable);
                if (readBinding != null) {
                    // The read arm creates the carrier: it is keyed once at
                    // its creation, by the read's own registration.
                    bindingsByValue.put(callable, readBinding);
                }
                return callable;
            }
            FunctionExecutionBinding existing = bindingsByValue.get(callable);
            if (existing != null && readBinding != null && !existing.equals(readBinding)) {
                throw new IllegalStateException("the cataloged callable of '"
                    + payload.module().path() + "#" + payload.name() + "' already"
                    + " carries the value-keyed binding " + existing + " (a read never"
                    + " re-keys the value-keyed map — a producer defect)");
            }
            return callable;
        }

        /**
         * The closed import kind of one read's module, resolved from the
         * reading unit's own {@code MODULE_IMPORT} record (the session's
         * own import facts — never a path guess, never another module's
         * record), or {@code null} when the unit records no import fact
         * for the module (the class-core carrier sessions), which keeps
         * the landed placeholder realization.
         */
        private ModuleImportKind importKindOf(UnitState unit, ModuleId module) {
            for (SemanticOp candidate : unit.unit.ops()) {
                if (candidate.kind() != SemanticOpKind.MODULE_IMPORT) {
                    continue;
                }
                KindPayload.ModuleImportPayload payload =
                    (KindPayload.ModuleImportPayload) candidate.payload();
                if (payload.resolvedModule().equals(module)) {
                    return payload.kind();
                }
            }
            return null;
        }

        /**
         * MODULE_IMPORT — the load-once initialization record. The tail's
         * stdlib slice imports {@code std/console} only: the stdlib
         * console algorithm executes inside {@code STDLIB_CALL}
         * ({@code CONSOLE_LOG}/{@code CONSOLE_ERROR}), so the import
         * record initializes no run state beyond the op terminal.
         */
        private String executeModuleImport(SemanticOp op) {
            KindPayload.ModuleImportPayload payload =
                (KindPayload.ModuleImportPayload) op.payload();
            return null;
        }

        /**
         * MODULE_INIT — the E8 module-init state machine: the op runs
         * its payload init block (the {@code MODULE_IMPORT}/
         * {@code EXPORT_*}/entry-delegation ops nested under it) exactly
         * once per run, under the closed
         * {@code UNINITIALIZED -> INITIALIZING -> INITIALIZED}
         * transition. The op START precedes the walk (the block's own
         * events follow), the SUCCESS terminal publishes
         * {@code state:INITIALIZED} on completion; a DEAL failure inside
         * the walk records {@code FAILED(error)} (no export publication)
         * and the generic op failure path publishes the op's single
         * FAILURE terminal with the identical error snapshot. A second
         * execution of an already-INITIALIZED module is a skip (once
         * after dependencies); a re-entrant or failed re-execution is a
         * producer defect, never a silent re-run.
         */
        private String executeModuleInit(SemanticOp op) {
            KindPayload.ModuleInitPayload payload =
                (KindPayload.ModuleInitPayload) op.payload();
            if (op.origin().parentOpId() != null) {
                throw new IllegalStateException("MODULE_INIT " + op.opId()
                    + " records the structural parent " + op.origin().parentOpId()
                    + " (the module-level envelope op is parentless — a wrong parent is a "
                    + "producer defect, never a silent re-parenting)");
            }
            ModuleInitLifecycle lifecycle = moduleInitLifecycles.get(payload.module());
            if (lifecycle == ModuleInitLifecycle.INITIALIZING) {
                throw new IllegalStateException("re-entrant MODULE_INIT of module "
                    + payload.module() + " (producer defect: the frontend rejects "
                    + "import cycles with E2005)");
            }
            if (lifecycle == ModuleInitLifecycle.INITIALIZED) {
                return "state:INITIALIZED";
            }
            if (lifecycle == ModuleInitLifecycle.FAILED) {
                throw new IllegalStateException("a second MODULE_INIT after a failed "
                    + "module init of " + payload.module()
                    + " (producer defect: the run's failure is terminal)");
            }
            moduleInitLifecycles.put(payload.module(), ModuleInitLifecycle.INITIALIZING);
            try {
                runBlock(payload.initBlock());
            } catch (DealFailure failure) {
                moduleInitLifecycles.put(payload.module(), ModuleInitLifecycle.FAILED);
                throw failure;
            } catch (ReturnSignal | LoopSignal signal) {
                moduleInitLifecycles.put(payload.module(), ModuleInitLifecycle.INITIALIZED);
                throw signal; // the module-init block never transfers
            }
            moduleInitLifecycles.put(payload.module(), ModuleInitLifecycle.INITIALIZED);
            return "state:INITIALIZED";
        }

        private String executeDiscard(SemanticOp op) {
            KindPayload.DiscardPayload payload = (KindPayload.DiscardPayload) op.payload();
            Value discarded = valueOf(payload.value());
            // The entry delegation discards the main-call result: record it
            // as the run result atom.
            if (isEntryDelegationDiscard(op)) {
                entryResultAtom = atomOf(discarded);
            }
            return null;
        }

        /** True iff the DISCARD is the module-init block's trailing entry delegation. */
        private boolean isEntryDelegationDiscard(SemanticOp op) {
            List<OpId> initOps = table.blockOps().get(unit.moduleInit().initBlock());
            if (initOps == null || initOps.isEmpty()
                    || !initOps.get(initOps.size() - 1).equals(op.opId())) {
                return false;
            }
            return true;
        }
    }
}
