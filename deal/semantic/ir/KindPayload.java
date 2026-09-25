package deal.semantic.ir;

import java.util.List;
import java.util.Objects;

/**
 * The closed kind-payload family of {@code deal.semantic-ir/1} (parent
 * "Closed operation kinds and execution contracts"; schema S4). Every
 * {@link SemanticOpKind} has exactly one mandatory payload shape — the
 * corresponding nested record below, one per kind, with the parent
 * operation table's exact fields. The typed records are the only typed
 * construction surface: every mandatory payload field is a constructor
 * parameter (a missing field cannot compile) and is null-checked, so the
 * closed shapes cannot be bypassed through typed construction. Cross-field
 * constraints (which selector subsets are admissible per kind, which
 * boundary triples are in the closed table, where
 * {@code ELIDED_BY_ADAPTER} may appear, …) are validator checks (T6), not
 * construction checks.
 *
 * <p>Execution contracts of these payloads are the construct epics'
 * (ISSUE-0234..0239); this sealed family pins shapes only. {@code opId},
 * source coordinates, and trace phase stay outside the snapshot digest;
 * payload fields are inside it.</p>
 */
public sealed interface KindPayload
    permits KindPayload.ConstPayload,
            KindPayload.UnaryPayload,
            KindPayload.BinaryPayload,
            KindPayload.StringConcatPayload,
            KindPayload.ArrayNewPayload,
            KindPayload.TableNewPayload,
            KindPayload.ArrayLengthPayload,
            KindPayload.MemberReadPayload,
            KindPayload.MemberWritePayload,
            KindPayload.MemberDeletePayload,
            KindPayload.IndexNormalizePayload,
            KindPayload.IndexReadPayload,
            KindPayload.IndexWritePayload,
            KindPayload.IndexDeletePayload,
            KindPayload.OptionalReadPayload,
            KindPayload.HasFieldPayload,
            KindPayload.BoundaryPayload,
            KindPayload.BindingAllocPayload,
            KindPayload.BindingInitPayload,
            KindPayload.BindingLoadPayload,
            KindPayload.BindingStorePayload,
            KindPayload.RecursiveGroupInitPayload,
            KindPayload.ClosureNewPayload,
            KindPayload.FunctionAdaptPayload,
            KindPayload.AssignPayload,
            KindPayload.DeletePayload,
            KindPayload.CallPayload,
            KindPayload.ExternalEntryPayload,
            KindPayload.CallbackInvokePayload,
            KindPayload.IntrinsicCallPayload,
            KindPayload.StdlibCallPayload,
            KindPayload.AsyncStartPayload,
            KindPayload.AwaitPayload,
            KindPayload.BranchPayload,
            KindPayload.LoopPayload,
            KindPayload.ForEachPayload,
            KindPayload.TryCatchPayload,
            KindPayload.ThrowPayload,
            KindPayload.ReturnPayload,
            KindPayload.BreakPayload,
            KindPayload.ContinuePayload,
            KindPayload.DiscardPayload,
            KindPayload.ClassDefaultPayload,
            KindPayload.ClassNewPayload,
            KindPayload.ClassFactoryPayload,
            KindPayload.FieldReadPayload,
            KindPayload.FieldWritePayload,
            KindPayload.FieldDeletePayload,
            KindPayload.JsonFromClassPayload,
            KindPayload.JsonToClassPayload,
            KindPayload.ModuleInitPayload,
            KindPayload.ModuleImportPayload,
            KindPayload.ExportReadPayload,
            KindPayload.ExportPublishPayload,
            KindPayload.EntryInvokePayload {

    /**
     * A payload that carries an exact closed selector ({@code UNARY},
     * {@code BINARY}, {@code STDLIB_CALL}); the operation-contract
     * snapshot's optional {@code selector} field is wired from this
     * accessor.
     */
    interface SelectorCarrying {

        /** The exact closed selector carried by this payload. */
        ClosedSelector selector();
    }

    /**
     * The closed callee reference of {@code CALL}/{@code ASYNC_START}
     * (parent D13). Exactly the three variants below; no other callee
     * shape exists.
     */
    sealed interface CallCallee
        permits CallCallee.Static, CallCallee.Indirect, CallCallee.Dynamic {

        /**
         * A static callee: the {@link FunctionExecutionBinding} is recorded
         * inline (DIRECT, HOST, EXTERNAL resolutions with a known binding).
         */
        record Static(FunctionExecutionBinding binding) implements CallCallee {

            public Static {
                Objects.requireNonNull(binding, "binding must not be null");
            }
        }

        /**
         * An indirect callee whose binding is statically registered: the
         * callee {@code ValueId} names an allocation identity whose
         * {@link FunctionExecutionBinding} is recorded in this unit's
         * {@code functionBindings}, so the validator resolves it and
         * derives the exact boundary cells; execution re-resolves the
         * same registration.
         */
        record Indirect(ValueId callee) implements CallCallee {

            public Indirect {
                Objects.requireNonNull(callee, "callee must not be null");
            }
        }

        /**
         * A dynamically resolved callee whose binding kind is unknown
         * until execution: the callee {@code ValueId}'s allocation
         * identity has no statically resolvable registration in this
         * unit (its producing allocation lives outside the unit — a
         * callback-delivered or host-response-materialized function
         * value, or a foreign-unit function identity flowing in), so the
         * runtime resolves the identity against the project registry at
         * execution and selects the execution shape — DEAL body, host,
         * external ({@code RETAINED_ABI}), or {@code SHARED_BODY} — with
         * its return-boundary kind and owner per the closed selection
         * ({@link DynamicReturnBoundaryProtocol}). A
         * {@code CALL} with a {@code Dynamic} callee records its return
         * boundary per runtime resolution class through
         * {@link CallPayload#dynamicReturnBoundary()} — never through
         * the single {@code returnBoundaryOpId} — and an
         * {@code ASYNC_START} records the single
         * {@code FUNCTION_RETURN} task cell of the {@code DEAL_BODY}
         * resolution (host/external/adapter resolutions execute zero
         * caller-side return boundaries).
         */
        record Dynamic(ValueId callee) implements CallCallee {

            public Dynamic {
                Objects.requireNonNull(callee, "callee must not be null");
            }
        }
    }

    /**
     * The return-boundary cells of a {@code CALL} whose callee is
     * {@link CallCallee.Dynamic}: exactly one recorded {@code BOUNDARY}
     * op id per runtime resolution class that executes a caller-side
     * return boundary, selected at execution by
     * {@link DynamicReturnBoundaryProtocol}.
     *
     * <ul>
     *   <li>{@code dealBodyBoundaryOpId} — the {@code FUNCTION_RETURN}
     *       cell of the DEAL-body resolution ({@code LoweredBody} and
     *       DEAL-body-source adapter bindings); executed by the callee's
     *       source {@code RETURN}.</li>
     *   <li>{@code hostBoundaryOpId} — the {@code HOST_TO_DEAL} +
     *       {@code HOST_SYNC_RETURN} cell of the host resolution
     *       ({@code HostFunction}, {@code HostFunctionValue}, and
     *       host-source adapter bindings); executed by the call op.</li>
     *   <li>{@code externalBoundaryOpId} — the {@code EXTERNAL_RETURN}
     *       cell of the retained-ABI external resolution
     *       ({@code ExternalFunction} with {@code RETAINED_ABI} and
     *       retained-ABI-source adapter bindings); executed by the call
     *       op.</li>
     * </ul>
     *
     * <p>A {@code SHARED_BODY} external resolution records no entry by
     * construction: it executes zero caller-side return boundaries — the
     * callee's {@code RETURN} under its {@code EXTERNAL_ENTRY} runs the
     * single {@code EXTERNAL_RETURN} in the callee unit and the CALL
     * terminal records the checked value without re-checking. The
     * three recorded cells carry mutually distinct closed kinds, so the
     * runtime selection is exactly one cell per resolution.</p>
     */
    record DynamicReturnBoundary(OpId dealBodyBoundaryOpId, OpId hostBoundaryOpId,
                                 OpId externalBoundaryOpId) {

        public DynamicReturnBoundary {
            Objects.requireNonNull(dealBodyBoundaryOpId,
                "dealBodyBoundaryOpId must not be null");
            Objects.requireNonNull(hostBoundaryOpId, "hostBoundaryOpId must not be null");
            Objects.requireNonNull(externalBoundaryOpId,
                "externalBoundaryOpId must not be null");
        }
    }

    /** One {@code TABLE_NEW} identifier-key/value pair (source order). */
    record TableEntry(String key, ValueId value) {

        public TableEntry {
            Objects.requireNonNull(key, "key must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** One provided field of {@code CLASS_NEW} (literal order). */
    record ProvidedField(String name, ValueId valueOpId) {

        public ProvidedField {
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(valueOpId, "valueOpId must not be null");
        }
    }

    /**
     * One field boundary of {@code CLASS_NEW} (declaration order). The
     * pinned kind subset is {@code CLASS_LITERAL_FIELD} (provided values)
     * or {@code CLASS_DEFAULT_FIELD} (defaulted values); membership in
     * that subset is a validator check over the closed table.
     */
    record FieldBoundary(String field, BoundaryKind kind, OpId boundaryOpId) {

        public FieldBoundary {
            Objects.requireNonNull(field, "field must not be null");
            Objects.requireNonNull(kind, "kind must not be null");
            Objects.requireNonNull(boundaryOpId, "boundaryOpId must not be null");
        }
    }

    /**
     * {@code CONST} — a canonical scalar. Out-of-range int literals never
     * reach the IR (E1036 frontend), so the signed32 value is exact.
     */
    record ConstPayload(ScalarValue value) implements KindPayload {

        public ConstPayload {
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** {@code UNARY} — one closed unary selector. */
    record UnaryPayload(UnarySelector selector) implements KindPayload, SelectorCarrying {

        public UnaryPayload {
            Objects.requireNonNull(selector, "selector must not be null");
        }
    }

    /**
     * {@code BINARY} — one closed binary selector plus the
     * {@code NULLABLE_*} payload fields: the inner descriptor and the side
     * mode {@code LEFT|RIGHT|BOTH} (only meaningful for the nullable
     * selectors; a validator check over the closed selector table).
     */
    record BinaryPayload(BinarySelector selector, RuntimeDescriptor innerDescriptor, NullableSide side)
        implements KindPayload, SelectorCarrying {

        public BinaryPayload {
            Objects.requireNonNull(selector, "selector must not be null");
        }
    }

    /**
     * {@code STRING_CONCAT} — the ordered string fragments/interpolations
     * in source order, concatenated after all operands complete.
     */
    record StringConcatPayload(List<ValueId> fragments) implements KindPayload {

        public StringConcatPayload(List<ValueId> fragments) {
            this.fragments = List.copyOf(fragments);
        }
    }

    /**
     * {@code ARRAY_NEW} — element descriptor, ordered values, and one
     * element-boundary op id per value (kind {@code ARRAY_LITERAL_ELEMENT},
     * policy {@code ARRAY_ELEMENT_DESCRIPTOR}); allocation happens only
     * after all element checks.
     */
    record ArrayNewPayload(RuntimeDescriptor elementDescriptor, List<ValueId> values,
                           List<OpId> elementBoundaryOpIds) implements KindPayload {

        public ArrayNewPayload(RuntimeDescriptor elementDescriptor, List<ValueId> values,
                               List<OpId> elementBoundaryOpIds) {
            this.elementDescriptor = Objects.requireNonNull(elementDescriptor, "elementDescriptor must not be null");
            this.values = List.copyOf(values);
            this.elementBoundaryOpIds = List.copyOf(elementBoundaryOpIds);
        }
    }

    /**
     * {@code TABLE_NEW} — ordered identifier-key/value pairs; a fresh
     * insertion-ordered table stored in source order.
     */
    record TableNewPayload(List<TableEntry> entries) implements KindPayload {

        public TableNewPayload(List<TableEntry> entries) {
            this.entries = List.copyOf(entries);
        }
    }

    /** {@code ARRAY_LENGTH} — the array value; result is a signed32 count. */
    record ArrayLengthPayload(ValueId arrayValue) implements KindPayload {

        public ArrayLengthPayload {
            Objects.requireNonNull(arrayValue, "arrayValue must not be null");
        }
    }

    /**
     * {@code MEMBER_READ} — table and string key; missing-aware read that
     * evaluates receiver then key exactly once.
     */
    record MemberReadPayload(ValueId table, String key) implements KindPayload {

        public MemberReadPayload {
            Objects.requireNonNull(table, "table must not be null");
            Objects.requireNonNull(key, "key must not be null");
        }
    }

    /**
     * {@code MEMBER_WRITE} — table, string key, and value. A commit op:
     * consumes the resolved receiver/key from the enclosing {@code ASSIGN}
     * chain, never re-evaluates expressions, commits at SUCCESS.
     */
    record MemberWritePayload(ValueId table, String key, ValueId value) implements KindPayload {

        public MemberWritePayload {
            Objects.requireNonNull(table, "table must not be null");
            Objects.requireNonNull(key, "key must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** {@code MEMBER_DELETE} — table and string key (commit op). */
    record MemberDeletePayload(ValueId table, String key) implements KindPayload {

        public MemberDeletePayload {
            Objects.requireNonNull(table, "table must not be null");
            Objects.requireNonNull(key, "key must not be null");
        }
    }

    /**
     * {@code INDEX_NORMALIZE} — index mode, raw key/index, and the current
     * length read at normalize time. A pure slot/key computation with
     * policy {@code NO_DEAL_FAILURE}; it never raises a DEAL failure —
     * negative/out-of-range enforcement happens only in the named
     * read/write/delete boundary policies.
     */
    record IndexNormalizePayload(IndexMode mode, ValueId rawKey, ValueId currentLength)
        implements KindPayload {

        public IndexNormalizePayload {
            Objects.requireNonNull(mode, "mode must not be null");
            Objects.requireNonNull(rawKey, "rawKey must not be null");
            Objects.requireNonNull(currentLength, "currentLength must not be null");
        }
    }

    /**
     * {@code INDEX_READ} — container, normalized slot/key, and the element
     * boundary (kind {@code ARRAY_ELEMENT_READ}, policy
     * {@code ARRAY_READ_INDEX_THEN_DESCRIPTOR}).
     */
    record IndexReadPayload(ValueId container, ValueId slot, OpId elementBoundaryOpId)
        implements KindPayload {

        public IndexReadPayload {
            Objects.requireNonNull(container, "container must not be null");
            Objects.requireNonNull(slot, "slot must not be null");
            Objects.requireNonNull(elementBoundaryOpId, "elementBoundaryOpId must not be null");
        }
    }

    /** {@code INDEX_WRITE} — container, normalized slot/key, and value (commit op). */
    record IndexWritePayload(ValueId container, ValueId slot, ValueId value) implements KindPayload {

        public IndexWritePayload {
            Objects.requireNonNull(container, "container must not be null");
            Objects.requireNonNull(slot, "slot must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** {@code INDEX_DELETE} — container and normalized slot/key (commit op). */
    record IndexDeletePayload(ValueId container, ValueId slot) implements KindPayload {

        public IndexDeletePayload {
            Objects.requireNonNull(container, "container must not be null");
            Objects.requireNonNull(slot, "slot must not be null");
        }
    }

    /**
     * {@code OPTIONAL_READ} — the present value (or internal missing), and
     * the inner descriptor. Missing maps to language null before a present
     * value is validated; {@code value} may be {@code null} exactly when
     * the slot is absent.
     */
    record OptionalReadPayload(ValueId value, boolean present, RuntimeDescriptor descriptor)
        implements KindPayload {

        public OptionalReadPayload {
            Objects.requireNonNull(descriptor, "descriptor must not be null");
        }
    }

    /** {@code HAS_FIELD} — checked receiver and key, each evaluated once. */
    record HasFieldPayload(ValueId receiver, String key) implements KindPayload {

        public HasFieldPayload {
            Objects.requireNonNull(receiver, "receiver must not be null");
            Objects.requireNonNull(key, "key must not be null");
        }
    }

    /**
     * {@code BOUNDARY} — the closed boundary kind, the checked descriptor,
     * the input value, and the boundary realization. The
     * {@code (kind, descriptor, policy)} triple must be a cell of the
     * closed boundary-assignment table (validator R-BOUNDARY-TRIPLE).
     */
    record BoundaryPayload(BoundaryKind kind, RuntimeDescriptor descriptor, ValueId input,
                           BoundaryRealization realization) implements KindPayload {

        public BoundaryPayload {
            Objects.requireNonNull(kind, "kind must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
            Objects.requireNonNull(input, "input must not be null");
            Objects.requireNonNull(realization, "realization must not be null");
        }
    }

    /**
     * {@code BINDING_ALLOC} — binding, scope, mutability, the
     * {@code DIRECT|SHARED_CELL} cell kind, and the generation counter;
     * allocates an uninitialized binding/cell.
     */
    record BindingAllocPayload(BindingId binding, BlockId scope, boolean mutable,
                               BindingCellKind cellKind, long generation) implements KindPayload {

        public BindingAllocPayload {
            Objects.requireNonNull(binding, "binding must not be null");
            Objects.requireNonNull(scope, "scope must not be null");
            Objects.requireNonNull(cellKind, "cellKind must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * {@code BINDING_INIT} — binding, generation, and the optional
     * initializer value; init once, with the boundary preceding the commit.
     */
    record BindingInitPayload(BindingId binding, long generation, ValueId value)
        implements KindPayload {

        public BindingInitPayload {
            Objects.requireNonNull(binding, "binding must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /** {@code BINDING_LOAD} — binding and generation (generation-checked load). */
    record BindingLoadPayload(BindingId binding, long generation) implements KindPayload {

        public BindingLoadPayload {
            Objects.requireNonNull(binding, "binding must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * {@code BINDING_STORE} — binding, generation, and the optional stored
     * value; the commit op for {@code VARIABLE} assignment (boundary
     * precedes commit).
     */
    record BindingStorePayload(BindingId binding, long generation, ValueId value)
        implements KindPayload {

        public BindingStorePayload {
            Objects.requireNonNull(binding, "binding must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /**
     * {@code RECURSIVE_GROUP_INIT} — the ordered bindings and functions of
     * a recursive group; identities are allocated first, then published
     * atomically.
     */
    record RecursiveGroupInitPayload(List<BindingId> bindings, List<FunctionId> functions)
        implements KindPayload {

        public RecursiveGroupInitPayload(List<BindingId> bindings, List<FunctionId> functions) {
            this.bindings = List.copyOf(bindings);
            this.functions = List.copyOf(functions);
        }
    }

    /**
     * {@code CLOSURE_NEW} — function, exact signature, ordered captures
     * (binding references per the spec), and the {@code LoweredBody}
     * binding; publishes a fresh function identity.
     */
    record ClosureNewPayload(FunctionId function, RuntimeDescriptor.Func signature,
                             List<BindingId> captures, FunctionExecutionBinding.LoweredBody binding)
        implements KindPayload {

        public ClosureNewPayload(FunctionId function, RuntimeDescriptor.Func signature,
                                 List<BindingId> captures, FunctionExecutionBinding.LoweredBody binding) {
            this.function = Objects.requireNonNull(function, "function must not be null");
            this.signature = Objects.requireNonNull(signature, "signature must not be null");
            this.captures = List.copyOf(captures);
            this.binding = Objects.requireNonNull(binding, "binding must not be null");
        }
    }

    /**
     * {@code FUNCTION_ADAPT} — source/target signatures, the closed
     * capture mode, the closed source reference, and the optional
     * immutability proof ({@code VALUE} over a binding source requires it;
     * D15 creation rule). Creation evaluates no thunk and reads no binding
     * except VALUE's single operand/load.
     */
    record FunctionAdaptPayload(RuntimeDescriptor.Func sourceSignature,
                                RuntimeDescriptor.Func targetSignature, CaptureMode mode,
                                AdaptSourceRef source, BindingImmutabilityProof proof)
        implements KindPayload {

        public FunctionAdaptPayload {
            Objects.requireNonNull(sourceSignature, "sourceSignature must not be null");
            Objects.requireNonNull(targetSignature, "targetSignature must not be null");
            Objects.requireNonNull(mode, "mode must not be null");
            Objects.requireNonNull(source, "source must not be null");
        }
    }

    /**
     * {@code ASSIGN} — target kind plus the ordered D14 address chain
     * {@code [containerOp?, keyOp?, valueOp, normalizeOp?, boundaryOps…, commitOp]}:
     * receiver → key → RHS → normalize → write check
     * ({@code ARRAY_ELEMENT_ASSIGNMENT}) → commit, with single evaluation;
     * FAIL commits nothing.
     */
    record AssignPayload(AssignTargetKind targetKind, List<OpId> childOps) implements KindPayload {

        public AssignPayload(AssignTargetKind targetKind, List<OpId> childOps) {
            this.targetKind = Objects.requireNonNull(targetKind, "targetKind must not be null");
            this.childOps = List.copyOf(childOps);
        }
    }

    /**
     * {@code DELETE} — target kind plus the ordered D14 address chain
     * {@code [containerOp?, keyOp?, normalizeOp?, boundaryOp? (ARRAY_SLOT only), commitOp]};
     * no RHS. The {@code ARRAY_SLOT} boundary is
     * {@code ARRAY_ELEMENT_DELETE} with {@code ARRAY_DELETE_BOUNDS};
     * table and class targets run no bounds boundary.
     */
    record DeletePayload(DeleteTargetKind targetKind, List<OpId> childOps) implements KindPayload {

        public DeletePayload(DeleteTargetKind targetKind, List<OpId> childOps) {
            this.targetKind = Objects.requireNonNull(targetKind, "targetKind must not be null");
            this.childOps = List.copyOf(childOps);
        }
    }

    /**
     * {@code CALL} — closed call mode, callee reference, exact signature,
     * parameter boundary op ids in one-based order, return boundary op id
     * (absent for EXTERNAL {@code SHARED_BODY}), the dynamic return
     * boundary set (exactly for a {@link CallCallee.Dynamic} callee),
     * body block (DIRECT), and external-entry ref (EXTERNAL
     * {@code SHARED_BODY}). The D13 machine owns execution;
     * parameter/return boundary kinds and policies come from the closed
     * boundary-assignment table.
     *
     * <p>Closed exclusivity (construction-checked): a {@code Dynamic}
     * callee is admissible only under {@link CallMode#INDIRECT}, records
     * exactly {@code dynamicReturnBoundary} (never the single
     * {@code returnBoundaryOpId} — the runtime selects the cell of the
     * resolved execution class); a {@code Static}/{@code Indirect} callee
     * records exactly the single {@code returnBoundaryOpId} (never
     * {@code dynamicReturnBoundary}). The validator repeats the same
     * exclusivity on the text surface.</p>
     */
    record CallPayload(CallMode mode, CallCallee callee, RuntimeDescriptor.Func signature,
                       List<OpId> parameterBoundaryOpIds, OpId returnBoundaryOpId,
                       DynamicReturnBoundary dynamicReturnBoundary,
                       BlockId bodyBlock, OpId externalEntryRef) implements KindPayload {

        public CallPayload(CallMode mode, CallCallee callee, RuntimeDescriptor.Func signature,
                           List<OpId> parameterBoundaryOpIds, OpId returnBoundaryOpId,
                           DynamicReturnBoundary dynamicReturnBoundary,
                           BlockId bodyBlock, OpId externalEntryRef) {
            this.mode = Objects.requireNonNull(mode, "mode must not be null");
            this.callee = Objects.requireNonNull(callee, "callee must not be null");
            this.signature = Objects.requireNonNull(signature, "signature must not be null");
            this.parameterBoundaryOpIds = List.copyOf(parameterBoundaryOpIds);
            this.returnBoundaryOpId = returnBoundaryOpId;
            this.dynamicReturnBoundary = dynamicReturnBoundary;
            this.bodyBlock = bodyBlock;
            this.externalEntryRef = externalEntryRef;
            boolean dynamic = callee instanceof CallCallee.Dynamic;
            if (dynamic && mode != CallMode.INDIRECT) {
                throw new IllegalArgumentException("a Dynamic callee is admissible only under "
                    + "CallMode INDIRECT, got " + mode);
            }
            if (dynamic && dynamicReturnBoundary == null) {
                throw new IllegalArgumentException("a Dynamic callee must record its dynamic "
                    + "return-boundary set");
            }
            if (dynamic && returnBoundaryOpId != null) {
                throw new IllegalArgumentException("a Dynamic callee records no single "
                    + "returnBoundaryOpId (the dynamic return-boundary set replaces it)");
            }
            if (!dynamic && dynamicReturnBoundary != null) {
                throw new IllegalArgumentException("only a Dynamic callee records the dynamic "
                    + "return-boundary set");
            }
        }
    }

    /**
     * {@code EXTERNAL_ENTRY} — the callee-unit invocation record for a
     * function callable across a shared/shadow edge: export name,
     * function, signature, sync/async marker, return boundary op id, and
     * the completion descriptor (async only, {@code null} for sync). One
     * static op per callable export; it runs no parameter boundaries
     * (caller-side {@code EXTERNAL_PARAMETER} runs exactly once).
     */
    record ExternalEntryPayload(String exportName, FunctionId function,
                                RuntimeDescriptor.Func signature, boolean async,
                                OpId returnBoundaryOpId, RuntimeDescriptor completionDescriptor)
        implements KindPayload {

        public ExternalEntryPayload {
            Objects.requireNonNull(exportName, "exportName must not be null");
            Objects.requireNonNull(function, "function must not be null");
            Objects.requireNonNull(signature, "signature must not be null");
            Objects.requireNonNull(returnBoundaryOpId, "returnBoundaryOpId must not be null");
        }
    }

    /**
     * {@code CALLBACK_INVOKE} — host-driven top-level invocation of a DEAL
     * function value: the bound function {@code ValueId}, its descriptor,
     * the {@code HOST_TO_DEAL} parameter boundary op ids, and the
     * {@code DEAL_TO_HOST} return boundary op id. Sync only.
     */
    record CallbackInvokePayload(ValueId function, RuntimeDescriptor.Func descriptor,
                                 List<OpId> parameterBoundaryOpIds, OpId returnBoundaryOpId)
        implements KindPayload {

        public CallbackInvokePayload(ValueId function, RuntimeDescriptor.Func descriptor,
                                     List<OpId> parameterBoundaryOpIds, OpId returnBoundaryOpId) {
            this.function = Objects.requireNonNull(function, "function must not be null");
            this.descriptor = Objects.requireNonNull(descriptor, "descriptor must not be null");
            this.parameterBoundaryOpIds = List.copyOf(parameterBoundaryOpIds);
            this.returnBoundaryOpId = Objects.requireNonNull(returnBoundaryOpId, "returnBoundaryOpId must not be null");
        }
    }

    /**
     * {@code INTRINSIC_CALL} — the closed conversion and one input. Zero
     * {@code BOUNDARY} child ops of any kind: the conversion policy
     * ({@code INT_CONVERSION}/{@code NUMBER_CONVERSION}) is the op's only
     * terminal check.
     */
    record IntrinsicCallPayload(IntrinsicKind kind, ValueId input) implements KindPayload {

        public IntrinsicCallPayload {
            Objects.requireNonNull(kind, "kind must not be null");
            Objects.requireNonNull(input, "input must not be null");
        }
    }

    /**
     * {@code STDLIB_CALL} — the closed stdlib function id, the ordered
     * argument values, and the effect capability. Arguments complete
     * left-to-right, then {@code STDLIB_PARAMETER} boundaries run in
     * order; the result passes {@code STDLIB_RETURN}; the op's
     * {@code failurePolicy} is the named algorithm policy from the closed
     * stdlib table. {@code TIME_NOW_MILLIS} is the 21st member (K7): zero
     * declared parameters, the declared {@code int} return boundary, and
     * the {@code INT32_RESULT} terminal.
     */
    record StdlibCallPayload(StdlibFunctionId function, List<ValueId> args,
                             SemanticCapability effectCapability)
        implements KindPayload, SelectorCarrying {

        public StdlibCallPayload(StdlibFunctionId function, List<ValueId> args,
                                 SemanticCapability effectCapability) {
            this.function = Objects.requireNonNull(function, "function must not be null");
            this.args = List.copyOf(args);
            this.effectCapability = Objects.requireNonNull(effectCapability, "effectCapability must not be null");
        }

        @Override
        public ClosedSelector selector() {
            return function;
        }
    }

    /**
     * {@code ASYNC_START} — callee reference, validator-derived
     * {@code AsyncStartSource}, parameter boundary mode, parameter
     * boundary op ids, completion descriptor, return boundary op id
     * (DEAL_BODY), host operation label (HOST), and the external
     * async-linkage record (EXTERNAL). {@code ELIDED_BY_ADAPTER} is
     * admissible only on the nested source op of an adapter-over-async
     * task (validator R-ELIDED-PLACEMENT).
     *
     * <p>Closed projection of a {@link CallCallee.Dynamic} callee
     * (construction-checked): the recorded {@code source} is
     * {@link AsyncStartSource#DEAL_BODY} — the only resolution whose
     * caller-recorded return boundary executes — and the recorded
     * {@code returnBoundaryOpId} is that resolution's single
     * {@code FUNCTION_RETURN} task cell; the runtime derives the
     * effective source from the resolved binding exactly like
     * {@code CALL(INDIRECT)}, and HOST/EXTERNAL/adapter-over-async
     * resolutions execute zero caller-side return boundaries
     * (their runtime linkage — operation label or
     * {@link ExternalAsyncLink} — binds at execution).</p>
     */
    record AsyncStartPayload(CallCallee callee, AsyncStartSource source,
                             ParameterBoundaryMode parameterBoundaryMode,
                             List<OpId> parameterBoundaryOpIds,
                             RuntimeDescriptor completionDescriptor, OpId returnBoundaryOpId,
                             String hostOperationLabel, ExternalAsyncLink externalAsyncLink)
        implements KindPayload {

        public AsyncStartPayload(CallCallee callee, AsyncStartSource source,
                                 ParameterBoundaryMode parameterBoundaryMode,
                                 List<OpId> parameterBoundaryOpIds,
                                 RuntimeDescriptor completionDescriptor, OpId returnBoundaryOpId,
                                 String hostOperationLabel, ExternalAsyncLink externalAsyncLink) {
            this.callee = Objects.requireNonNull(callee, "callee must not be null");
            this.source = Objects.requireNonNull(source, "source must not be null");
            this.parameterBoundaryMode = Objects.requireNonNull(parameterBoundaryMode, "parameterBoundaryMode must not be null");
            this.parameterBoundaryOpIds = List.copyOf(parameterBoundaryOpIds);
            this.completionDescriptor = Objects.requireNonNull(completionDescriptor, "completionDescriptor must not be null");
            this.returnBoundaryOpId = returnBoundaryOpId;
            this.hostOperationLabel = hostOperationLabel;
            this.externalAsyncLink = externalAsyncLink;
            if (callee instanceof CallCallee.Dynamic && source != AsyncStartSource.DEAL_BODY) {
                throw new IllegalArgumentException("a Dynamic ASYNC_START records source "
                    + "DEAL_BODY (the only resolution whose caller-recorded return boundary "
                    + "executes); the runtime derives the effective source from the resolved "
                    + "binding");
            }
        }
    }

    /**
     * {@code AWAIT} — the consumed token, the completion descriptor, and
     * the completion boundary op id. Operation failure wins (the identical
     * error, never a re-check or synthesized copy); otherwise the
     * {@code ASYNC_COMPLETION} boundary validates the completion value at
     * the await site. The token is consumed exactly once (validator
     * R-TOKEN-REUSE).
     */
    record AwaitPayload(AsyncTokenId token, RuntimeDescriptor completionDescriptor,
                        OpId completionBoundaryOpId) implements KindPayload {

        public AwaitPayload {
            Objects.requireNonNull(token, "token must not be null");
            Objects.requireNonNull(completionDescriptor, "completionDescriptor must not be null");
            Objects.requireNonNull(completionBoundaryOpId, "completionBoundaryOpId must not be null");
        }
    }

    /**
     * {@code BRANCH} — the closed control selector, the condition value,
     * and the child block ids; executes only the selected block, and the
     * logical selectors return the selected boolean. {@code alternateBlock}
     * may be {@code null} when the shape has no alternate block.
     */
    record BranchPayload(ControlSelector selector, ValueId condition,
                         BlockId selectedBlock, BlockId alternateBlock) implements KindPayload {

        public BranchPayload {
            Objects.requireNonNull(selector, "selector must not be null");
            Objects.requireNonNull(condition, "condition must not be null");
            Objects.requireNonNull(selectedBlock, "selectedBlock must not be null");
        }
    }

    /**
     * {@code LOOP} — {@code WHILE|FOR} (the admissible selector subset is a
     * validator check), init/condition/body/update blocks; no speculative
     * body/update execution and matching exits only. {@code initBlock} and
     * {@code updateBlock} may be {@code null} ({@code WHILE} shapes).
     */
    record LoopPayload(ControlSelector selector, BlockId initBlock, ValueId condition,
                       BlockId bodyBlock, BlockId updateBlock) implements KindPayload {

        public LoopPayload {
            Objects.requireNonNull(selector, "selector must not be null");
            Objects.requireNonNull(condition, "condition must not be null");
            Objects.requireNonNull(bodyBlock, "bodyBlock must not be null");
        }
    }

    /**
     * {@code FOR_EACH} — the closed iteration mode, the iterable (evaluated
     * once), the binding generation (fresh binding each iteration), and
     * the body block. {@code STRING_SCALARS} validates the complete scalar
     * sequence before the first binding.
     */
    record ForEachPayload(IterationMode mode, ValueId iterable, BindingId binding,
                          long generation, BlockId body) implements KindPayload {

        public ForEachPayload {
            Objects.requireNonNull(mode, "mode must not be null");
            Objects.requireNonNull(iterable, "iterable must not be null");
            Objects.requireNonNull(binding, "binding must not be null");
            Objects.requireNonNull(body, "body must not be null");
            if (generation < 0) {
                throw new IllegalArgumentException("generation must be >= 0, got " + generation);
            }
        }
    }

    /** {@code TRY_CATCH} — try block, catch binding, and catch block; catches DEAL failures only. */
    record TryCatchPayload(BlockId tryBlock, BindingId catchBinding, BlockId catchBlock)
        implements KindPayload {

        public TryCatchPayload {
            Objects.requireNonNull(tryBlock, "tryBlock must not be null");
            Objects.requireNonNull(catchBinding, "catchBinding must not be null");
            Objects.requireNonNull(catchBlock, "catchBlock must not be null");
        }
    }

    /**
     * {@code THROW} — the Error value; transfers to the nearest catch/host
     * and publishes no success (policy {@code THROW_TRANSFER} preserves
     * the supplied code/message/origin).
     */
    record ThrowPayload(ValueId errorValue) implements KindPayload {

        public ThrowPayload {
            Objects.requireNonNull(errorValue, "errorValue must not be null");
        }
    }

    /**
     * {@code RETURN} — the optional value, the returning function, the
     * enclosing invocation op id ({@code CALL} | {@code CALLBACK_INVOKE} |
     * {@code ASYNC_START} body task | {@code EXTERNAL_ENTRY}), and the
     * return boundary op id. The return boundary is checked exactly once:
     * {@code RETURN} executes it for body-bearing calls, for
     * DEAL-body-source adapter calls, for callback invocations of bodies,
     * and for {@code SHARED_BODY} external calls (in the callee unit); the
     * CALL terminal records but never re-checks.
     */
    record ReturnPayload(ValueId value, FunctionId function, OpId enclosingInvocationOpId,
                         OpId returnBoundaryOpId) implements KindPayload {

        public ReturnPayload {
            Objects.requireNonNull(function, "function must not be null");
            Objects.requireNonNull(enclosingInvocationOpId, "enclosingInvocationOpId must not be null");
            Objects.requireNonNull(returnBoundaryOpId, "returnBoundaryOpId must not be null");
        }
    }

    /** {@code BREAK} — the matching loop id; matching loop-ID transfer only. */
    record BreakPayload(OpId loopId) implements KindPayload {

        public BreakPayload {
            Objects.requireNonNull(loopId, "loopId must not be null");
        }
    }

    /** {@code CONTINUE} — the matching loop id; matching loop-ID transfer only. */
    record ContinuePayload(OpId loopId) implements KindPayload {

        public ContinuePayload {
            Objects.requireNonNull(loopId, "loopId must not be null");
        }
    }

    /** {@code DISCARD} — the discarded value; its effects are already completed. */
    record DiscardPayload(ValueId value) implements KindPayload {

        public DiscardPayload {
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /**
     * {@code CLASS_DEFAULT} — class, field, and default block; produces the
     * default value once per construction in declaration order and carries
     * no boundary of its own.
     */
    record ClassDefaultPayload(ClassId classId, String field, BlockId defaultBlock)
        implements KindPayload {

        public ClassDefaultPayload {
            Objects.requireNonNull(classId, "classId must not be null");
            Objects.requireNonNull(field, "field must not be null");
            Objects.requireNonNull(defaultBlock, "defaultBlock must not be null");
        }
    }

    /**
     * {@code CLASS_NEW} — classId, layout, provided fields in literal
     * order, the closed {@code defaultOwner}, the optional
     * {@code CLASS_DEFAULT} child op ids (LOCAL), the optional factory ref
     * (SHARED_FACTORY/RETAINED_ABI), and the field boundary ids in
     * declaration order. D16 construction order: provided values (literal
     * order) → default application → provided application with extra-key
     * rejection → field validation (declaration order) → tag; zero return
     * boundaries.
     *
     * <p>The closed owner set's {@code HOST_DEFAULTS}, {@code FFI_PLAN},
     * and {@code BUILTIN_DEFAULTS} members are the project lowering's class
     * registration seeds (ISSUE-0631). {@code BUILTIN_DEFAULTS} is the
     * builtin {@code Error} construction (ISSUE-0619) and
     * {@code HOST_DEFAULTS} the host declaration class construction over
     * the loaded {@code <C>_defaults} entry (ISSUE-0624): provided fields
     * in literal order, one {@code CLASS_LITERAL_FIELD} boundary per
     * provided field in declaration order, the null factory ref, and the
     * empty default-op list. {@code FFI_PLAN} is the extern-C C-struct
     * construction over the loaded {@code <C>_plan} entry (ISSUE-0666):
     * the same provided-field boundaries, the null factory ref, the empty
     * default-op list, and no {@code CLASS_DEFAULT_FIELD} boundary — the
     * omitted fields' evaluators are the loaded plan's. {@code RETAINED_ABI}
     * is never produced on the production path; a payload carrying an
     * unrealized owner is rejected fail-closed by the validator and by
     * every emitter/oracle owner arm.</p>
     */
    record ClassNewPayload(ClassId classId, ClassLayout layout, List<ProvidedField> providedFields,
                           DefaultOwner defaultOwner, List<OpId> classDefaultOpIds,
                           ClassFactoryId classFactoryRef, List<FieldBoundary> fieldBoundaries)
        implements KindPayload {

        public ClassNewPayload(ClassId classId, ClassLayout layout, List<ProvidedField> providedFields,
                               DefaultOwner defaultOwner, List<OpId> classDefaultOpIds,
                               ClassFactoryId classFactoryRef, List<FieldBoundary> fieldBoundaries) {
            this.classId = Objects.requireNonNull(classId, "classId must not be null");
            this.layout = Objects.requireNonNull(layout, "layout must not be null");
            this.providedFields = List.copyOf(providedFields);
            this.defaultOwner = Objects.requireNonNull(defaultOwner, "defaultOwner must not be null");
            this.classDefaultOpIds = List.copyOf(classDefaultOpIds);
            this.classFactoryRef = classFactoryRef;
            this.fieldBoundaries = List.copyOf(fieldBoundaries);
        }
    }

    /**
     * {@code CLASS_FACTORY} — the declaring module's default-application op
     * for an exported class: classId, the {@code CLASS_DEFAULT} child op
     * ids in declaration order, and the triggering caller op ref. Runs
     * zero boundaries and zero return boundaries; policy
     * {@code CLASS_CONSTRUCTION}.
     */
    record ClassFactoryPayload(ClassId classId, List<OpId> classDefaultOpIds, OpId callerOpRef)
        implements KindPayload {

        public ClassFactoryPayload(ClassId classId, List<OpId> classDefaultOpIds, OpId callerOpRef) {
            this.classId = Objects.requireNonNull(classId, "classId must not be null");
            this.classDefaultOpIds = List.copyOf(classDefaultOpIds);
            this.callerOpRef = Objects.requireNonNull(callerOpRef, "callerOpRef must not be null");
        }
    }

    /** {@code FIELD_READ} — class value, class, and field; presence-aware read. */
    record FieldReadPayload(ValueId classValue, ClassId classId, String field)
        implements KindPayload {

        public FieldReadPayload {
            Objects.requireNonNull(classValue, "classValue must not be null");
            Objects.requireNonNull(classId, "classId must not be null");
            Objects.requireNonNull(field, "field must not be null");
        }
    }

    /** {@code FIELD_WRITE} — class value, class, field, and value (commit op). */
    record FieldWritePayload(ValueId classValue, ClassId classId, String field, ValueId value)
        implements KindPayload {

        public FieldWritePayload {
            Objects.requireNonNull(classValue, "classValue must not be null");
            Objects.requireNonNull(classId, "classId must not be null");
            Objects.requireNonNull(field, "field must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** {@code FIELD_DELETE} — class value, class, and field (commit op). */
    record FieldDeletePayload(ValueId classValue, ClassId classId, String field)
        implements KindPayload {

        public FieldDeletePayload {
            Objects.requireNonNull(classValue, "classValue must not be null");
            Objects.requireNonNull(classId, "classId must not be null");
            Objects.requireNonNull(field, "field must not be null");
        }
    }

    /**
     * {@code JSON_FROM_CLASS} — class layout and JSON string; class or
     * null; parse/key/field failure returns null (policy
     * {@code JSON_FROM_NULL}).
     */
    record JsonFromClassPayload(ClassLayout layout, ValueId jsonString) implements KindPayload {

        public JsonFromClassPayload {
            Objects.requireNonNull(layout, "layout must not be null");
            Objects.requireNonNull(jsonString, "jsonString must not be null");
        }
    }

    /**
     * {@code JSON_TO_CLASS} — class value and layout; deterministic JSON;
     * first unsupported/cycle/nonfinite failure (policy
     * {@code JSON_TO_ERROR}).
     */
    record JsonToClassPayload(ValueId classValue, ClassLayout layout) implements KindPayload {

        public JsonToClassPayload {
            Objects.requireNonNull(classValue, "classValue must not be null");
            Objects.requireNonNull(layout, "layout must not be null");
        }
    }

    /**
     * {@code MODULE_INIT} — module, resolved imports, and the init block;
     * {@code UNINITIALIZED→INITIALIZING→INITIALIZED} with
     * {@code FAILED(error)} recorded on failure (no exports published).
     */
    record ModuleInitPayload(ModuleId module, List<ModuleId> imports, BlockId initBlock)
        implements KindPayload {

        public ModuleInitPayload(ModuleId module, List<ModuleId> imports, BlockId initBlock) {
            this.module = Objects.requireNonNull(module, "module must not be null");
            this.imports = List.copyOf(imports);
            this.initBlock = Objects.requireNonNull(initBlock, "initBlock must not be null");
        }
    }

    /**
     * {@code MODULE_IMPORT} — raw specifier, resolved module, the closed
     * {@code COMPILED|STDLIB|HOST} kind, and the import's ordered alias
     * cells; initialize/load once (cycle is frontend E2005; host load
     * failures use E8011).
     *
     * <p><b>Alias cells (the one recorded payload addition of the
     * project-lowering cutover).</b> {@code aliasCells} is the ordered
     * {@link BindingId} list of the import declaration's alias
     * allocation(s) — the alias&#8596;import join the checker pins. The
     * op's completion is the pinned initializing write of every cell it
     * names; an alias cell never carries a {@code BINDING_INIT}. An
     * absent/empty list is the no-alias-cell case (operation-free
     * synthetic units and the pre-addition text surface); the canonical
     * dump of the op changes by exactly this list, the closed payload
     * record set and the closed {@code SemanticOpKind} set are unchanged,
     * and the {@code deal.semantic-ir/1} version text is unchanged.
     *
     * @param rawSpecifier   the raw specifier as written; non-null
     * @param resolvedModule the resolved module identity; non-null
     * @param kind           the closed module-import kind; non-null
     * @param aliasCells     the ordered alias cells the completion
     *                       writes; non-null (empty for none)
     */
    record ModuleImportPayload(String rawSpecifier, ModuleId resolvedModule, ModuleImportKind kind,
                               List<BindingId> aliasCells)
        implements KindPayload {

        public ModuleImportPayload {
            Objects.requireNonNull(rawSpecifier, "rawSpecifier must not be null");
            Objects.requireNonNull(resolvedModule, "resolvedModule must not be null");
            Objects.requireNonNull(kind, "kind must not be null");
            aliasCells = List.copyOf(Objects.requireNonNull(aliasCells,
                "aliasCells must not be null"));
            for (BindingId cell : aliasCells) {
                Objects.requireNonNull(cell, "aliasCells entries must not be null");
            }
        }

        /**
         * The no-alias-cell form: an operation-free synthetic unit's
         * import record (absence/empty is the no-alias-cell case).
         */
        public ModuleImportPayload(String rawSpecifier, ModuleId resolvedModule,
                                   ModuleImportKind kind) {
            this(rawSpecifier, resolvedModule, kind, List.of());
        }
    }

    /** {@code EXPORT_READ} — module, export name, descriptor, and value (checked read). */
    record ExportReadPayload(ModuleId module, String name, RuntimeDescriptor descriptor, ValueId value)
        implements KindPayload {

        public ExportReadPayload {
            Objects.requireNonNull(module, "module must not be null");
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /** {@code EXPORT_PUBLISH} — module, export name, descriptor, and value (atomic publication after boundary). */
    record ExportPublishPayload(ModuleId module, String name, RuntimeDescriptor descriptor, ValueId value)
        implements KindPayload {

        public ExportPublishPayload {
            Objects.requireNonNull(module, "module must not be null");
            Objects.requireNonNull(name, "name must not be null");
            Objects.requireNonNull(descriptor, "descriptor must not be null");
            Objects.requireNonNull(value, "value must not be null");
        }
    }

    /**
     * {@code ENTRY_INVOKE} — the entry module and its exact
     * {@code main(): null} function; delegates exactly one
     * {@code CALL(DIRECT)} to main and exits the program after the
     * terminal; no separate boundary.
     */
    record EntryInvokePayload(ModuleId module, FunctionId mainFunction) implements KindPayload {

        public EntryInvokePayload {
            Objects.requireNonNull(module, "module must not be null");
            Objects.requireNonNull(mainFunction, "mainFunction must not be null");
        }
    }
}
