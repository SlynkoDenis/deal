package deal.semantic;

import deal.diagnostics.CompilerDiagnostic;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassFactoryRegistry;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.FailureContractRegistry;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.JsonDefaultChildTable;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringFailureDetail;
import deal.semantic.ir.OpId;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SharedFactoryFacts;
import deal.semantic.ir.StructuredBodyTable;
import deal.semantic.ir.ValueId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * The production-time class-construction validator of
 * {@code deal.semantic-ir/1} (class-construction-jsonable-operations
 * K-D11; ISSUE-0516): validates one {@link LoweredModuleUnit} together
 * with the class epic's production records — the
 * {@link StructuredBodyTable} block membership, the
 * {@link ClassFactoryRegistry} factory registrations, the
 * {@link JsonDefaultChildTable} per-site default children, the module's
 * own {@link ExternalModuleInterface} entry (the pre-allocated
 * {@code constructionEntry} facts), and the imported-construction
 * {@link SharedFactoryFacts} context — against the pinned class-op
 * coherence contracts, producing E6005 outside the foundation
 * validator's closed 14-condition rule set (the
 * {@link ControlFlowValidator}/{@link BindingsProductionValidator}
 * precedent).
 *
 * <p><b>Scope.</b> The validator consumes only the unit, the production
 * records, and interface facts — no target knowledge, no AST, no
 * checker state. It never executes operations; it checks the structural
 * coherence the {@link deal.semantic.ir.ClassOpsExecutor}'s
 * fail-closed discipline pins (the executor defects are the runtime
 * mirror of these production checks). The foundation validator's pinned
 * schema subsets (the {@code CLASS_FACTORY} {@code CLASS_CONSTRUCTION}
 * policy row, the {@code JSON_FROM_NULL}/{@code JSON_TO_ERROR} rows,
 * the {@code CLASS_LITERAL_FIELD}/{@code CLASS_DEFAULT_FIELD}
 * descriptor-kind cells, and the
 * {@code UNTYPED_CLASS_INPUT}/{@code OPTIONAL_FIELD_READ}/
 * {@code CLASS_FIELD_ASSIGNMENT} cells) stay the foundation's checks:
 * this validator adds no rules to the closed 14-condition set.</p>
 *
 * <p><b>Pinned checks (first-failure order).</b></p>
 * <ol>
 *   <li>{@link #FACTORY_COHERENCE} — the factory&#8596;constructionEntry
 *       bijection for exported classes and the factory payload shape
 *       (K-D2/K-D5): every exported class's pre-allocated
 *       {@code constructionEntry} registers exactly one
 *       {@code CLASS_FACTORY} op; every registry key is exactly one
 *       exported class's entry; every produced {@code CLASS_FACTORY}
 *       op is registered; the factory op is a detached static op (no
 *       {@code parentOpId}), carries {@code CLASS_CONSTRUCTION}, the
 *       class's id, a {@link ValueId} result of the class descriptor,
 *       zero boundary children, and {@code classDefaultOpIds} = exactly
 *       the required-present defaulted fields' {@code CLASS_DEFAULT}
 *       op ids in declaration order; the unit carries exactly one
 *       {@code CLASS_DEFAULT} op per defaulted {@code (classId,
 *       field)}.</li>
 *   <li>{@link #CONSTRUCTION_COHERENCE} — the {@code CLASS_NEW} payload
 *       coherence (K-D4): the layout carries the payload's classId and
 *       resolves to exactly the payload's layout; the default-owner
 *       shape is closed (LOCAL for same-module classes with the
 *       omitted-default child list; SHARED_FACTORY for imported classes
 *       with the interface's {@code constructionEntry} and empty child
 *       list; RETAINED_ABI is never produced — E10's; and the three
 *       class registration seeds HOST_DEFAULTS/FFI_PLAN/BUILTIN_DEFAULTS
 *       of ISSUE-0631 are rejected as fail-closed producer defects until
 *       their construction children realize them); every provided
 *       name is a declared field; {@code fieldBoundaries} = exactly one
 *       {@code CLASS_LITERAL_FIELD} per provided field plus one
 *       {@code CLASS_DEFAULT_FIELD} per omitted required-present
 *       defaulted field in declaration order; each boundary child
 *       resolves, is parented to the {@code CLASS_NEW} op, carries the
 *       field's declared descriptor, the descriptor-kind policy, a
 *       {@code RuntimeValidation} realization, and the pinned K-D4
 *       input wiring (the provided value op for literal fields; the
 *       field's {@code CLASS_DEFAULT} child result for LOCAL defaulted
 *       fields; the owner {@code CLASS_FACTORY} op's result
 *       {@link ValueId} for SHARED_FACTORY defaulted fields); and the
 *       op's boundary children are exactly the payload's listed ids in
 *       order.</li>
 *   <li>{@link #FIELD_OPERATION_SHAPE} — the field-operation child
 *       shapes (K-D6): {@code FIELD_READ} children =
 *       {@code [UNTYPED_CLASS_INPUT, OPTIONAL_FIELD_READ]},
 *       {@code FIELD_WRITE} children =
 *       {@code [UNTYPED_CLASS_INPUT, CLASS_FIELD_ASSIGNMENT]},
 *       {@code FIELD_DELETE} children =
 *       {@code [UNTYPED_CLASS_INPUT]} — each parented to the op with
 *       the pinned descriptors/inputs/policies and no other boundary
 *       children; the class id and the field resolve in the layout
 *       context; required-field deletes never appear.</li>
 *   <li>{@link #DEFAULT_BLOCK_ADMISSION} — the default-block admission
 *       (K-D3): every binding reference of a {@code CLASS_DEFAULT}
 *       block's closure (direct loads, nested closure captures, and
 *       adapter-thunk captures) resolves to an allocation inside the
 *       default closure itself or in the module-init block — an
 *       enclosing-region free reference is invalid.</li>
 *   <li>{@link #JSON_LAYOUT_COHERENCE} — the JSON-walker coherence
 *       (K-D8/K-D10): the {@code JSON_FROM_CLASS}/
 *       {@code JSON_TO_CLASS} policies; the payload layout is exactly
 *       the unit's own layout of a {@code @jsonable} class; the
 *       {@code JsonDefaultChildTable} entry of every
 *       {@code JSON_FROM_CLASS} op lists exactly the class's
 *       required-present defaulted fields' {@code CLASS_DEFAULT} child
 *       ids in declaration order (no orphans); and every nested
 *       class-typed field of every jsonable layout resolves — own
 *       classes through the unit's layouts (exported own classes with a
 *       registered factory, the JSON nested-factory trigger), imported
 *       classes through the {@link SharedFactoryFacts} context.</li>
 * </ol>
 *
 * <p><b>Failure and determinism.</b> Every rejection is exactly one E6005
 * ({@code BACKEND_LOWERING}) carrying a {@link LoweringFailureDetail} with
 * {@code capability CLASSES}, the failing rule name, the unit's
 * {@code semanticProfile}, {@code irVersion deal.semantic-ir/1}, the
 * module, and the {@code ClassConstructionValidator} origin, built by
 * {@link FailureContractRegistry#e6005(LoweringFailureDetail)}. Checks
 * traverse the unit's ops in op order and the records in map iteration
 * order; equal inputs produce byte-identical diagnostics. The pass is
 * pure (no mutation) and linear in ops plus the block/boundary edges of
 * the default-block closures.</p>
 */
public final class ClassConstructionValidator {

    /** The factory/registry bijection and factory payload rule (K-D2/K-D5). */
    public static final String FACTORY_COHERENCE = "FACTORY_COHERENCE";

    /** The {@code CLASS_NEW} payload, layout, boundary, and input-wiring rule (K-D4). */
    public static final String CONSTRUCTION_COHERENCE = "CONSTRUCTION_COHERENCE";

    /** The field-operation boundary-child shape rule (K-D6). */
    public static final String FIELD_OPERATION_SHAPE = "FIELD_OPERATION_SHAPE";

    /** The default-block reference admission rule (K-D3). */
    public static final String DEFAULT_BLOCK_ADMISSION = "DEFAULT_BLOCK_ADMISSION";

    /** The JSON-walker default-child and nested-layout resolution rule (K-D8/K-D10). */
    public static final String JSON_LAYOUT_COHERENCE = "JSON_LAYOUT_COHERENCE";

    private ClassConstructionValidator() {
        // Static surface; no instances.
    }

    /**
     * Validates one unit plus the class epic's production records and
     * interface facts against the pinned class-op coherence contracts.
     * The first violation in the pinned rule order is the returned
     * E6005; {@code empty} on the pass path.
     *
     * @param unit            the lowered module unit; non-null
     * @param table           the produced block-membership table; non-null
     * @param factories       the produced factory registrations; non-null
     * @param jsonDefaults    the produced JSON default-child table; non-null
     * @param ownInterface    the module's own interface index entry (the
     *                        pre-allocated {@code constructionEntry} ids
     *                        and the {@code hasDefault} facts); non-null
     * @param sharedFactories the imported-construction facts by
     *                        {@link ClassId} — the imported classes'
     *                        layouts, interface entries, factory op ids,
     *                        and factory results; must cover every
     *                        imported class the unit's class constructs
     *                        reference (constructions and nested
     *                        jsonable fields alike); non-null
     * @return the first E6005 diagnostic, or {@code empty}
     */
    public static Optional<CompilerDiagnostic> validate(
            LoweredModuleUnit unit,
            StructuredBodyTable table,
            ClassFactoryRegistry factories,
            JsonDefaultChildTable jsonDefaults,
            ExternalModuleInterface ownInterface,
            Map<ClassId, SharedFactoryFacts> sharedFactories) {
        Objects.requireNonNull(unit, "unit must not be null");
        Objects.requireNonNull(table, "table must not be null");
        Objects.requireNonNull(factories, "factories must not be null");
        Objects.requireNonNull(jsonDefaults, "jsonDefaults must not be null");
        Objects.requireNonNull(ownInterface, "ownInterface must not be null");
        Objects.requireNonNull(sharedFactories, "sharedFactories must not be null");
        Context context = new Context(unit, table, factories, jsonDefaults, ownInterface,
            sharedFactories);
        Optional<CompilerDiagnostic> failure = context.checkFactoryCoherence();
        if (failure.isPresent()) {
            return failure;
        }
        failure = context.checkConstructionCoherence();
        if (failure.isPresent()) {
            return failure;
        }
        failure = context.checkFieldOperationShapes();
        if (failure.isPresent()) {
            return failure;
        }
        failure = context.checkDefaultBlockAdmission();
        if (failure.isPresent()) {
            return failure;
        }
        return context.checkJsonLayoutCoherence();
    }

    // =========================================================================
    // The per-validation context (pure, deterministic)
    // =========================================================================

    private static final class Context {

        private final LoweredModuleUnit unit;
        private final StructuredBodyTable table;
        private final ClassFactoryRegistry factories;
        private final JsonDefaultChildTable jsonDefaults;
        private final ExternalModuleInterface ownInterface;
        private final Map<ClassId, SharedFactoryFacts> sharedFactories;

        /** The unit's produced ops by {@link OpId} (pinned lookup). */
        private final Map<OpId, SemanticOp> opsById = new LinkedHashMap<>();

        /**
         * The layout-resolution context (K-D11): the unit's own
         * {@code classLayouts} overlaid by the imported classes' owner
         * layouts.
         */
        private final Map<ClassId, ClassLayout> layoutContext = new LinkedHashMap<>();

        /**
         * The interface-resolution context: the module's own interface
         * entries plus the imported classes' interface entries.
         */
        private final Map<ClassId, ClassInterface> interfaceContext = new LinkedHashMap<>();

        Context(LoweredModuleUnit unit, StructuredBodyTable table,
                ClassFactoryRegistry factories, JsonDefaultChildTable jsonDefaults,
                ExternalModuleInterface ownInterface,
                Map<ClassId, SharedFactoryFacts> sharedFactories) {
            this.unit = unit;
            this.table = table;
            this.factories = factories;
            this.jsonDefaults = jsonDefaults;
            this.ownInterface = ownInterface;
            this.sharedFactories = Map.copyOf(sharedFactories);
            for (SemanticOp op : unit.ops()) {
                opsById.put(op.opId(), op);
            }
            layoutContext.putAll(unit.classLayouts());
            // The compiler-owned builtin Error layout (ISSUE-0619; K13 item
            // 1): the builtin class is a compiler-owned layout entry in
            // every unit's resolution context — the same entry the project
            // lowering seeds — so the Error literal's CLASS_NEW resolves its
            // classId exactly like a declared class and the payload's layout
            // is checkable against the one authority.
            layoutContext.put(ClassId.ERROR, ClassLayout.BUILTIN_ERROR);
            for (Map.Entry<ClassId, SharedFactoryFacts> entry : this.sharedFactories
                    .entrySet()) {
                layoutContext.put(entry.getKey(), entry.getValue().layout());
                interfaceContext.put(entry.getKey(), entry.getValue().interfaceEntry());
            }
            for (ClassInterface entry : ownInterface.classes()) {
                interfaceContext.put(entry.classId(), entry);
            }
        }

        /** Builds the E6005 diagnostic of one failing rule. */
        private CompilerDiagnostic defect(String rule, String origin) {
            return FailureContractRegistry.e6005(new LoweringFailureDetail(
                unit.moduleId().path(), SemanticCapability.CLASSES, rule,
                unit.semanticProfile(), LoweredModuleUnit.FORMAT_VERSION,
                "ClassConstructionValidator " + rule + " (" + origin + ")"));
        }

        private Optional<CompilerDiagnostic> fail(String rule, String origin) {
            return Optional.of(defect(rule, origin));
        }

        /** The op named by the id, or {@code null}. */
        private SemanticOp op(OpId opId) {
            return opsById.get(opId);
        }

        /**
         * The unit's {@code CLASS_DEFAULT} op of one class and field, or
         * {@code null}. At most one such op may exist (the uniqueness is
         * {@link #FACTORY_COHERENCE}'s check, run before every consumer).
         */
        private SemanticOp defaultOp(ClassId classId, String field) {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_DEFAULT) {
                    continue;
                }
                KindPayload.ClassDefaultPayload payload =
                    (KindPayload.ClassDefaultPayload) op.payload();
                if (payload.classId().equals(classId) && payload.field().equals(field)) {
                    return op;
                }
            }
            return null;
        }

        /** The declared field of one layout, or {@code null}. */
        private static ClassLayout.FieldLayout fieldOf(ClassLayout layout, String name) {
            for (ClassLayout.FieldLayout field : layout.fields()) {
                if (field.name().equals(name)) {
                    return field;
                }
            }
            return null;
        }

        /** The pinned {@code OPTIONAL_FIELD_READ} result descriptor wrap (K-D6). */
        private static RuntimeDescriptor readResultDescriptorOf(
                ClassLayout.FieldLayout field) {
            RuntimeDescriptor declared = field.descriptor();
            if (!field.required() && !(declared instanceof RuntimeDescriptor.Nullable)) {
                return new RuntimeDescriptor.Nullable(declared);
            }
            return declared;
        }

        /** The descriptor-kind rule policy of one checked descriptor. */
        private static FailurePolicyId descriptorKindPolicy(RuntimeDescriptor descriptor) {
            return descriptor instanceof RuntimeDescriptor.Func
                ? FailurePolicyId.FUNCTION_SIGNATURE : FailurePolicyId.TYPE_DESCRIPTOR;
        }

        /** The class descriptor of one class id (the canonical nominal descriptor). */
        private static RuntimeDescriptor.Class classDescriptor(ClassId classId) {
            return new RuntimeDescriptor.Class(classId);
        }

        /** The boundary ops parented to one op, in unit op order. */
        private List<SemanticOp> boundaryChildren(SemanticOp owner) {
            List<SemanticOp> children = new ArrayList<>();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() == SemanticOpKind.BOUNDARY
                        && owner.opId().equals(op.origin().parentOpId())) {
                    children.add(op);
                }
            }
            return children;
        }

        /** The shared factory facts of one imported class, or {@code null}. */
        private SharedFactoryFacts factsOf(ClassId classId) {
            return sharedFactories.get(classId);
        }

        /**
         * The pinned boundary-child shape (kind, descriptor, input,
         * descriptor-kind policy, runtime-validation realization,
         * parentage). {@code null} on the pass path, otherwise the
         * failing origin text. A {@code null} {@code input} argument
         * skips the input comparison (the caller checks the input
         * wiring separately).
         */
        private String boundaryShapeViolation(SemanticOp child, SemanticOp owner,
                                              BoundaryKind kind,
                                              RuntimeDescriptor descriptor,
                                              ValueId input) {
            if (child.kind() != SemanticOpKind.BOUNDARY) {
                return "child " + child.opId() + " of " + owner.kind() + " " + owner.opId()
                    + " is " + child.kind() + ", not BOUNDARY";
            }
            if (!owner.opId().equals(child.origin().parentOpId())) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " records parentOpId "
                    + child.origin().parentOpId() + ", not the owning op";
            }
            KindPayload.BoundaryPayload payload = (KindPayload.BoundaryPayload) child.payload();
            if (payload.kind() != kind) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " carries kind " + payload.kind() + ", not " + kind;
            }
            if (!payload.descriptor().equals(descriptor)) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " carries descriptor "
                    + payload.descriptor().canonicalSpecText() + ", not "
                    + descriptor.canonicalSpecText();
            }
            if (input != null && !payload.input().equals(input)) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " carries input " + payload.input() + ", not " + input;
            }
            if (child.failurePolicy() != descriptorKindPolicy(descriptor)) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " carries policy " + child.failurePolicy()
                    + ", not the descriptor-kind rule's " + descriptorKindPolicy(descriptor);
            }
            if (!(payload.realization() instanceof BoundaryRealization.RuntimeValidation)) {
                return "boundary child " + child.opId() + " of " + owner.kind() + " "
                    + owner.opId() + " carries realization " + payload.realization()
                    + ", not a runtime validation (every class-op boundary is a "
                    + "RuntimeValidation cell)";
            }
            return null;
        }

        // =====================================================================
        // 1. FACTORY_COHERENCE
        // =====================================================================

        Optional<CompilerDiagnostic> checkFactoryCoherence() {
            // (a) Exactly one CLASS_DEFAULT op per defaulted (classId,
            // field): a duplicate default child is a malformed
            // construction shape (every consumer — the factory payload,
            // the LOCAL CLASS_NEW child list, and the JSON default-child
            // table — names exactly one op per field).
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_DEFAULT) {
                    continue;
                }
                KindPayload.ClassDefaultPayload payload =
                    (KindPayload.ClassDefaultPayload) op.payload();
                SemanticOp other = defaultOp(payload.classId(), payload.field());
                if (!other.opId().equals(op.opId())) {
                    return fail(FACTORY_COHERENCE, "two CLASS_DEFAULT ops (" + other.opId()
                        + " and " + op.opId() + ") exist for " + payload.classId() + "."
                        + payload.field() + ": the pinned shape carries exactly one "
                        + "default child per defaulted field");
                }
            }

            // (b) The exported classes' default-op coverage against the
            // interface hasDefault facts: every defaulted field carries
            // exactly one CLASS_DEFAULT op, every non-defaulted field
            // none.
            for (ClassInterface entry : ownInterface.classes()) {
                for (deal.semantic.ir.FieldInterface field : entry.fields()) {
                    SemanticOp defaultOp = defaultOp(entry.classId(), field.name());
                    if (field.hasDefault() && defaultOp == null) {
                        return fail(FACTORY_COHERENCE, "defaulted field '" + field.name()
                            + "' of exported class " + entry.classId() + " has no "
                            + "CLASS_DEFAULT op in the unit: the declaration arm emits "
                            + "one per defaulted field");
                    }
                    if (!field.hasDefault() && defaultOp != null) {
                        return fail(FACTORY_COHERENCE, "non-defaulted field '"
                            + field.name() + "' of exported class " + entry.classId()
                            + " carries a CLASS_DEFAULT op (" + defaultOp.opId()
                            + "): only defaulted fields produce default ops");
                    }
                }
            }

            // (c) The factory/constructionEntry bijection and the factory
            // payload shape for every exported class.
            Map<ClassFactoryId, ClassId> entryOwners = new LinkedHashMap<>();
            for (ClassInterface entry : ownInterface.classes()) {
                ClassFactoryId constructionEntry = entry.constructionEntry();
                if (entryOwners.containsKey(constructionEntry)) {
                    return fail(FACTORY_COHERENCE, "two exported classes ("
                        + entryOwners.get(constructionEntry) + " and " + entry.classId()
                        + ") share constructionEntry " + constructionEntry
                        + ": the pre-allocated ids are a bijection");
                }
                entryOwners.put(constructionEntry, entry.classId());
                OpId factoryOpId = factories.factoryFor(constructionEntry);
                if (factoryOpId == null) {
                    return fail(FACTORY_COHERENCE, "exported class " + entry.classId()
                        + " has no factory registered under constructionEntry "
                        + constructionEntry + ": one CLASS_FACTORY per exported class");
                }
                SemanticOp factory = op(factoryOpId);
                if (factory == null) {
                    return fail(FACTORY_COHERENCE, "the registered factory op "
                        + factoryOpId + " of " + entry.classId() + " is not a produced "
                        + "op of the unit");
                }
                Optional<CompilerDiagnostic> shape = checkFactoryShape(factory, entry);
                if (shape.isPresent()) {
                    return shape;
                }
            }
            for (ClassFactoryId constructionEntry : factories.factories().keySet()) {
                if (!entryOwners.containsKey(constructionEntry)) {
                    return fail(FACTORY_COHERENCE, "constructionEntry " + constructionEntry
                        + " is registered in the factory registry but names no exported "
                        + "class of the module's interface (the registry keys are exactly "
                        + "the exported classes' entries)");
                }
            }

            // (d) Every produced CLASS_FACTORY op is registered under
            // exactly one construction entry.
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_FACTORY) {
                    continue;
                }
                KindPayload.ClassFactoryPayload payload =
                    (KindPayload.ClassFactoryPayload) op.payload();
                boolean registered = false;
                for (Map.Entry<ClassFactoryId, OpId> binding
                        : factories.factories().entrySet()) {
                    if (binding.getValue().equals(op.opId())) {
                        if (registered) {
                            return fail(FACTORY_COHERENCE, "factory op " + op.opId()
                                + " is registered under two construction entries");
                        }
                        registered = true;
                        ClassId owner = entryOwners.get(binding.getKey());
                        if (!payload.classId().equals(owner)) {
                            return fail(FACTORY_COHERENCE, "factory op " + op.opId()
                                + " of class " + payload.classId() + " is registered "
                                + "under " + binding.getKey() + " (the entry of "
                                + owner + ")");
                        }
                    }
                }
                if (!registered) {
                    return fail(FACTORY_COHERENCE, "factory op " + op.opId() + " of "
                        + payload.classId() + " is not registered in the factory "
                        + "registry: every produced CLASS_FACTORY is the construction "
                        + "entry of exactly one exported class");
                }
            }
            return Optional.empty();
        }

        /** The pinned factory shape of one exported class's factory op. */
        private Optional<CompilerDiagnostic> checkFactoryShape(SemanticOp factory,
                                                               ClassInterface entry) {
            if (factory.kind() != SemanticOpKind.CLASS_FACTORY) {
                return fail(FACTORY_COHERENCE, "the registered op " + factory.opId()
                    + " of " + entry.classId() + " is " + factory.kind()
                    + ", not CLASS_FACTORY");
            }
            if (factory.failurePolicy() != FailurePolicyId.CLASS_CONSTRUCTION) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId() + " of "
                    + entry.classId() + " carries policy " + factory.failurePolicy()
                    + ", not the pinned CLASS_CONSTRUCTION");
            }
            KindPayload.ClassFactoryPayload payload =
                (KindPayload.ClassFactoryPayload) factory.payload();
            if (!payload.classId().equals(entry.classId())) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                    + " registered under " + entry.classId() + "'s constructionEntry "
                    + "carries classId " + payload.classId());
            }
            if (factory.origin().parentOpId() != null) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                    + " records parentOpId " + factory.origin().parentOpId()
                    + ": the factory is a detached static op, never parented (its "
                    + "executed parentOpId is the triggering caller op at execution)");
            }
            if (!(factory.result() instanceof ValueId)) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                    + " publishes result " + factory.result() + ", not a ValueId "
                    + "(the default-filled transfer instance)");
            }
            if (!(factory.resultType() instanceof RuntimeDescriptor.Class resultClass)
                    || !resultClass.classId().equals(entry.classId())) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                    + " publishes result type " + factory.resultType() + ", not the "
                    + "class descriptor of " + entry.classId());
            }
            if (!boundaryChildren(factory).isEmpty()) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                    + " has boundary children: the factory runs zero boundaries and "
                    + "zero return boundaries");
            }
            // classDefaultOpIds = exactly the required-present defaulted
            // fields' CLASS_DEFAULT op ids in declaration order.
            List<String> expected = new ArrayList<>();
            for (deal.semantic.ir.FieldInterface field : entry.fields()) {
                if (!field.optional() && field.hasDefault()) {
                    expected.add(field.name());
                }
            }
            List<OpId> listed = payload.classDefaultOpIds();
            if (listed.size() != expected.size()) {
                return fail(FACTORY_COHERENCE, "factory op " + factory.opId() + " lists "
                    + listed.size() + " CLASS_DEFAULT children for " + expected.size()
                    + " required-present defaulted fields: the pinned payload lists "
                    + "exactly those fields' op ids in declaration order");
            }
            ClassLayout layout = layoutContext.get(entry.classId());
            if (layout == null) {
                return fail(FACTORY_COHERENCE, "exported class " + entry.classId()
                    + " has no layout in the unit's classLayouts (the factory fills the "
                    + "declared layout)");
            }
            for (int i = 0; i < expected.size(); i++) {
                String fieldName = expected.get(i);
                SemanticOp child = op(listed.get(i));
                if (child == null) {
                    return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                        + " lists CLASS_DEFAULT child " + listed.get(i) + " (field '"
                        + fieldName + "') which is not a produced op of the unit");
                }
                if (child.kind() != SemanticOpKind.CLASS_DEFAULT) {
                    return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                        + " lists child " + listed.get(i) + " of kind " + child.kind()
                        + " for field '" + fieldName + "', not CLASS_DEFAULT");
                }
                KindPayload.ClassDefaultPayload childPayload =
                    (KindPayload.ClassDefaultPayload) child.payload();
                if (!childPayload.classId().equals(entry.classId())
                        || !childPayload.field().equals(fieldName)) {
                    return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                        + " lists child " + listed.get(i) + " for "
                        + childPayload.classId() + "." + childPayload.field()
                        + ", not " + entry.classId() + "." + fieldName);
                }
                if (child.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                    return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                        + " lists CLASS_DEFAULT child " + listed.get(i) + " carrying "
                        + "policy " + child.failurePolicy() + ", not NO_DEAL_FAILURE");
                }
                ClassLayout.FieldLayout fieldLayout = fieldOf(layout, fieldName);
                if (fieldLayout == null || !fieldLayout.required()) {
                    return fail(FACTORY_COHERENCE, "factory op " + factory.opId()
                        + " lists CLASS_DEFAULT child " + listed.get(i) + " for field '"
                        + fieldName + "' which is not a required declared field of "
                        + entry.classId());
                }
            }
            return Optional.empty();
        }

        // =====================================================================
        // 2. CONSTRUCTION_COHERENCE
        // =====================================================================

        Optional<CompilerDiagnostic> checkConstructionCoherence() {
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_NEW) {
                    continue;
                }
                Optional<CompilerDiagnostic> failure = checkClassNew(op);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            return Optional.empty();
        }

        private Optional<CompilerDiagnostic> checkClassNew(SemanticOp op) {
            if (op.failurePolicy() != FailurePolicyId.CLASS_CONSTRUCTION) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                    + " carries policy " + op.failurePolicy()
                    + ", not the pinned CLASS_CONSTRUCTION");
            }
            KindPayload.ClassNewPayload payload =
                (KindPayload.ClassNewPayload) op.payload();
            // Class/layout identity: the layout carries the payload's
            // classId and resolves to exactly the payload's layout.
            if (!payload.classId().equals(payload.layout().classId())) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                    + " carries classId " + payload.classId() + " and a layout of "
                    + payload.layout().classId() + ": the layout must carry the "
                    + "payload's classId");
            }
            ClassLayout resolved = layoutContext.get(payload.classId());
            if (resolved == null) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                    + " classId " + payload.classId() + " does not resolve in the "
                    + "layout context (the unit's classLayouts plus the imported "
                    + "classes' layouts)");
            }
            if (!resolved.equals(payload.layout())) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                    + " carries a layout that differs from the resolved layout of "
                    + payload.classId() + ": the payload's layout must be exactly the "
                    + "resolved layout");
            }
            boolean own = unit.classLayouts().containsKey(payload.classId());

            // The closed default-owner shape.
            List<String> providedNames = new ArrayList<>();
            Map<String, ValueId> providedIds = new LinkedHashMap<>();
            for (KindPayload.ProvidedField field : payload.providedFields()) {
                providedNames.add(field.name());
                providedIds.put(field.name(), field.valueOpId());
            }
            // Provided-field declarations: every provided name is a
            // declared field of the layout (K-D11 — the E8007 extra-key
            // projection remains the executor's unvalidated-input
            // contract, unreachable on a validated unit).
            for (String name : providedNames) {
                if (fieldOf(resolved, name) == null) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " provides field '" + name + "' which is not a declared "
                        + "field of " + payload.classId());
                }
            }
            List<String> expectedDefaults = new ArrayList<>();
            ValueId sharedFactoryResult = null;
            switch (payload.defaultOwner()) {
                case LOCAL -> {
                    if (!own) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " of imported class " + payload.classId() + " carries "
                            + "defaultOwner LOCAL: imported classes construct through "
                            + "the owner's CLASS_FACTORY (SHARED_FACTORY), never LOCAL");
                    }
                    if (payload.classFactoryRef() != null) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " carries classFactoryRef " + payload.classFactoryRef()
                            + " under LOCAL: the pinned LOCAL shape carries a null "
                            + "factory ref");
                    }
                    for (ClassLayout.FieldLayout field : resolved.fields()) {
                        if (field.required() && defaultOp(payload.classId(),
                                field.name()) != null
                                && !providedNames.contains(field.name())) {
                            expectedDefaults.add(field.name());
                        }
                    }
                    if (payload.classDefaultOpIds().size() != expectedDefaults.size()) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " (LOCAL) lists " + payload.classDefaultOpIds().size()
                            + " CLASS_DEFAULT children for " + expectedDefaults.size()
                            + " omitted required-present defaulted fields: the pinned "
                            + "child list names exactly those fields' op ids in "
                            + "declaration order");
                    }
                    for (int i = 0; i < expectedDefaults.size(); i++) {
                        Optional<CompilerDiagnostic> child =
                            checkDefaultChild(op, payload.classDefaultOpIds().get(i),
                                expectedDefaults.get(i), resolved);
                        if (child.isPresent()) {
                            return child;
                        }
                    }
                }
                case SHARED_FACTORY -> {
                    if (own) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " of same-module class " + payload.classId() + " carries "
                            + "defaultOwner SHARED_FACTORY: same-module literals stay "
                            + "LOCAL");
                    }
                    if (payload.classFactoryRef() == null) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " of imported class " + payload.classId() + " carries a "
                            + "null classFactoryRef under SHARED_FACTORY: the pinned "
                            + "shape carries the interface's constructionEntry");
                    }
                    if (!payload.classDefaultOpIds().isEmpty()) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " (SHARED_FACTORY) lists " + payload.classDefaultOpIds()
                            + ": the pinned imported shape carries an empty child list "
                            + "(defaults transfer to the owner's factory)");
                    }
                    SharedFactoryFacts facts = factsOf(payload.classId());
                    if (facts == null) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " of imported class " + payload.classId() + " has no "
                            + "shared-factory facts in the context: SHARED_FACTORY "
                            + "construction without the owner's factory facts is never "
                            + "produced (the RETAINED_ABI deferral)");
                    }
                    if (!facts.interfaceEntry().constructionEntry()
                            .equals(payload.classFactoryRef())) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " carries classFactoryRef " + payload.classFactoryRef()
                            + ", not the interface's constructionEntry "
                            + facts.interfaceEntry().constructionEntry() + " of "
                            + payload.classId());
                    }
                    sharedFactoryResult = facts.factoryResult();
                    for (ClassLayout.FieldLayout field : resolved.fields()) {
                        if (field.required() && !providedNames.contains(field.name())) {
                            expectedDefaults.add(field.name());
                        }
                    }
                }
                case RETAINED_ABI -> {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " carries defaultOwner RETAINED_ABI: the retained ABI "
                        + "transfer is E10's (ISSUE-0239) and is never produced in "
                        + "this epic — the lowerer defers with RETAINED_ABI_DEFERRED");
                }
                case HOST_DEFAULTS, FFI_PLAN -> {
                    // The declaration-class owners are the project
                    // lowering's class registration seeds (ISSUE-0631): a
                    // registration fact, never a construction shape. Their
                    // construction execution is the construction children's;
                    // until it lands every consumer rejects them as a
                    // fail-closed producer defect — no default evaluation and
                    // no emission.
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " carries defaultOwner " + payload.defaultOwner()
                        + ": the declaration-class owners are class registration"
                        + " seeds (ISSUE-0631) and their construction is not"
                        + " realized in this slice — a fail-closed producer defect,"
                        + " never executed or default-evaluated");
                }
                case BUILTIN_DEFAULTS -> {
                    // The builtin Error construction (ISSUE-0619; K13 items
                    // 2-4): the owner is admissible for exactly the builtin
                    // class identity, over exactly the compiler-owned
                    // layout, with the null factory ref, the empty
                    // default-op list, and no CLASS_DEFAULT_FIELD boundary
                    // (the omitted fields take the compiler constant empty
                    // string at the construction site).
                    if (!ClassId.ERROR.equals(payload.classId())) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " carries defaultOwner BUILTIN_DEFAULTS for class "
                            + payload.classId() + ": the builtin-defaults owner"
                            + " is admissible only for the builtin Error class "
                            + ClassId.ERROR.text() + " (a non-builtin class under"
                            + " BUILTIN_DEFAULTS is a fail-closed producer defect)");
                    }
                    if (!payload.layout().equals(ClassLayout.BUILTIN_ERROR)) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " under BUILTIN_DEFAULTS carries a layout other than"
                            + " the compiler-owned builtin Error layout (exactly the"
                            + " two string required-present fields code and"
                            + " message): a foreign layout is a fail-closed"
                            + " producer defect");
                    }
                    if (payload.classFactoryRef() != null) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " carries classFactoryRef " + payload.classFactoryRef()
                            + " under BUILTIN_DEFAULTS: the builtin Error"
                            + " construction carries a null factory ref (the"
                            + " builtin defaults are compiler constants, never a"
                            + " factory transfer)");
                    }
                    if (!payload.classDefaultOpIds().isEmpty()) {
                        return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                            + " (BUILTIN_DEFAULTS) lists "
                            + payload.classDefaultOpIds()
                            + ": the builtin Error construction carries an empty"
                            + " child list (the omitted fields take the compiler"
                            + " constant empty string at the construction site)");
                    }
                    for (KindPayload.FieldBoundary entry : payload.fieldBoundaries()) {
                        if (entry.kind() != BoundaryKind.CLASS_LITERAL_FIELD) {
                            return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW "
                                + op.opId() + " field-boundary entry for '"
                                + entry.field() + "' carries kind " + entry.kind()
                                + ", not CLASS_LITERAL_FIELD: the builtin Error"
                                + " construction carries exactly one"
                                + " CLASS_LITERAL_FIELD boundary per provided field"
                                + " and no CLASS_DEFAULT_FIELD (the omitted fields"
                                + " take the compiler constant empty string)");
                        }
                    }
                }
                default -> {
                    // Defensive: an owner outside the closed set can only
                    // arrive from a forged payload, and it never gets a
                    // construction shape.
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " carries defaultOwner " + payload.defaultOwner()
                        + ": an owner outside the closed default-ownership set"
                        + " is a fail-closed producer defect");
                }
            }

            // The pinned field-boundary list: exactly one entry per
            // provided field (CLASS_LITERAL_FIELD) and per omitted
            // required-present defaulted field (CLASS_DEFAULT_FIELD) in
            // declaration order; omitted optionals get no boundary.
            List<String> expectedBoundaries = new ArrayList<>();
            List<BoundaryKind> expectedKinds = new ArrayList<>();
            for (ClassLayout.FieldLayout field : resolved.fields()) {
                if (providedNames.contains(field.name())) {
                    expectedBoundaries.add(field.name());
                    expectedKinds.add(BoundaryKind.CLASS_LITERAL_FIELD);
                } else if (expectedDefaults.contains(field.name())) {
                    expectedBoundaries.add(field.name());
                    expectedKinds.add(BoundaryKind.CLASS_DEFAULT_FIELD);
                }
            }
            List<KindPayload.FieldBoundary> boundaries = payload.fieldBoundaries();
            if (boundaries.size() != expectedBoundaries.size()) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId() + " carries "
                    + boundaries.size() + " field-boundary entries for "
                    + expectedBoundaries.size() + " present fields: the pinned shape "
                    + "carries exactly one boundary per provided field and per "
                    + "omitted required-present defaulted field in declaration order");
            }
            List<SemanticOp> parentedChildren = boundaryChildren(op);
            if (parentedChildren.size() != boundaries.size()) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId() + " parents "
                    + parentedChildren.size() + " boundary children for "
                    + boundaries.size() + " payload entries: the op's boundary children "
                    + "are exactly the payload's listed ids");
            }
            for (int i = 0; i < boundaries.size(); i++) {
                KindPayload.FieldBoundary entry = boundaries.get(i);
                if (!entry.field().equals(expectedBoundaries.get(i))) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " field-boundary entry " + i + " names '" + entry.field()
                        + "': the pinned declaration order names '"
                        + expectedBoundaries.get(i) + "'");
                }
                if (entry.kind() != expectedKinds.get(i)) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " field-boundary entry for '" + entry.field() + "' carries "
                        + "kind " + entry.kind() + ", not " + expectedKinds.get(i));
                }
                SemanticOp child = op(entry.boundaryOpId());
                if (child == null) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " names boundary child " + entry.boundaryOpId() + " which is "
                        + "not a produced op of the unit");
                }
                if (!child.opId().equals(parentedChildren.get(i).opId())) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " payload boundary order does not match the op's parented "
                        + "children: entry " + i + " names " + entry.boundaryOpId()
                        + " but the i-th parented child is "
                        + parentedChildren.get(i).opId());
                }
                ClassLayout.FieldLayout fieldLayout = fieldOf(resolved, entry.field());
                String shape = boundaryShapeViolation(child, op, entry.kind(),
                    fieldLayout.descriptor(), null);
                if (shape != null) {
                    return fail(CONSTRUCTION_COHERENCE, shape);
                }
                KindPayload.BoundaryPayload boundaryPayload =
                    (KindPayload.BoundaryPayload) child.payload();
                // The K-D4 input wiring.
                ValueId pinnedInput;
                if (entry.kind() == BoundaryKind.CLASS_LITERAL_FIELD) {
                    pinnedInput = providedIds.get(entry.field());
                } else {
                    if (payload.defaultOwner() == DefaultOwner.SHARED_FACTORY) {
                        pinnedInput = sharedFactoryResult;
                    } else {
                        SemanticOp defaultChild = defaultOp(payload.classId(),
                            entry.field());
                        if (defaultChild == null || !(defaultChild.result()
                                instanceof ValueId resultId)) {
                            return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                                + " names CLASS_DEFAULT_FIELD for '" + entry.field()
                                + "' without a CLASS_DEFAULT child publishing a "
                                + "ValueId result");
                        }
                        pinnedInput = resultId;
                    }
                }
                if (pinnedInput == null) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " boundary for '" + entry.field() + "' has no pinned input "
                        + "(a literal field without a provided value)");
                }
                if (!boundaryPayload.input().equals(pinnedInput)) {
                    return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + op.opId()
                        + " boundary " + child.opId() + " carries input "
                        + boundaryPayload.input() + ", not the pinned " + pinnedInput
                        + " (the provided value op for CLASS_LITERAL_FIELD; the "
                        + "field's CLASS_DEFAULT child result for LOCAL; the owner "
                        + "factory result for SHARED_FACTORY)");
                }
            }
            return Optional.empty();
        }

        /** The pinned LOCAL CLASS_DEFAULT child of one field. */
        private Optional<CompilerDiagnostic> checkDefaultChild(SemanticOp owner,
                                                               OpId childId,
                                                               String fieldName,
                                                               ClassLayout layout) {
            SemanticOp child = op(childId);
            if (child == null) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + owner.opId()
                    + " lists CLASS_DEFAULT child " + childId + " (field '" + fieldName
                    + "') which is not a produced op of the unit");
            }
            if (child.kind() != SemanticOpKind.CLASS_DEFAULT) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + owner.opId()
                    + " lists child " + childId + " of kind " + child.kind()
                    + " for field '" + fieldName + "', not CLASS_DEFAULT");
            }
            KindPayload.ClassDefaultPayload payload =
                (KindPayload.ClassDefaultPayload) child.payload();
            if (!payload.classId().equals(layout.classId())
                    || !payload.field().equals(fieldName)) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + owner.opId()
                    + " lists child " + childId + " for " + payload.classId() + "."
                    + payload.field() + ", not " + layout.classId() + "." + fieldName);
            }
            if (child.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                return fail(CONSTRUCTION_COHERENCE, "CLASS_NEW " + owner.opId()
                    + " lists CLASS_DEFAULT child " + childId + " carrying policy "
                    + child.failurePolicy() + ", not NO_DEAL_FAILURE");
            }
            return Optional.empty();
        }

        // =====================================================================
        // 3. FIELD_OPERATION_SHAPE
        // =====================================================================

        Optional<CompilerDiagnostic> checkFieldOperationShapes() {
            for (SemanticOp op : unit.ops()) {
                switch (op.kind()) {
                    case FIELD_READ -> {
                        Optional<CompilerDiagnostic> failure = checkFieldRead(op);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                    case FIELD_WRITE -> {
                        Optional<CompilerDiagnostic> failure = checkFieldWrite(op);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                    case FIELD_DELETE -> {
                        Optional<CompilerDiagnostic> failure = checkFieldDelete(op);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                    default -> {
                        // Not a field op.
                    }
                }
            }
            return Optional.empty();
        }

        private Optional<CompilerDiagnostic> checkFieldRead(SemanticOp op) {
            if (op.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_READ " + op.opId()
                    + " carries policy " + op.failurePolicy()
                    + ", not the pinned NO_DEAL_FAILURE");
            }
            KindPayload.FieldReadPayload payload =
                (KindPayload.FieldReadPayload) op.payload();
            List<SemanticOp> children = boundaryChildren(op);
            if (children.size() != 2) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_READ " + op.opId() + " parents "
                    + children.size() + " boundary children: the pinned shape is "
                    + "exactly [UNTYPED_CLASS_INPUT, OPTIONAL_FIELD_READ]");
            }
            String receiver = boundaryShapeViolation(children.get(0), op,
                BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor(payload.classId()),
                payload.classValue());
            if (receiver != null) {
                return fail(FIELD_OPERATION_SHAPE, receiver);
            }
            if (!(op.result() instanceof ValueId readResult)) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_READ " + op.opId()
                    + " publishes result " + op.result() + ", not a ValueId (the "
                    + "OPTIONAL_FIELD_READ input is the op's own result)");
            }
            // The pinned OPTIONAL_FIELD_READ descriptor is the read's
            // checked result descriptor — the op's own resultType (the
            // checker's optional-read wrap). When the layout resolves, the
            // wrap must agree with the field's declared descriptor too.
            if (!(op.resultType() instanceof RuntimeDescriptor readDescriptor)) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_READ " + op.opId()
                    + " publishes result type " + op.resultType() + ", not a "
                    + "descriptor: the pinned OPTIONAL_FIELD_READ descriptor is the "
                    + "read's checked result descriptor");
            }
            String field = boundaryShapeViolation(children.get(1), op,
                BoundaryKind.OPTIONAL_FIELD_READ, readDescriptor, readResult);
            if (field != null) {
                return fail(FIELD_OPERATION_SHAPE, field);
            }
            ClassLayout layout = layoutContext.get(payload.classId());
            ClassLayout.FieldLayout fieldLayout = layout == null
                ? null : fieldOf(layout, payload.field());
            if (fieldLayout == null) {
                // An unresolvable layout/field is admitted for the
                // cross-module read arm (the receiver guard is the
                // runtime's); the checker's declared-field fact is the
                // declaration-side authority.
                return Optional.empty();
            }
            if (!readResultDescriptorOf(fieldLayout).equals(readDescriptor)) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_READ " + op.opId()
                    + " of " + payload.classId() + "." + payload.field()
                    + " publishes result descriptor "
                    + readDescriptor.canonicalSpecText() + ", not the checker's "
                    + "optional-read wrap "
                    + readResultDescriptorOf(fieldLayout).canonicalSpecText());
            }
            return Optional.empty();
        }

        private Optional<CompilerDiagnostic> checkFieldWrite(SemanticOp op) {
            if (op.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_WRITE " + op.opId()
                    + " carries policy " + op.failurePolicy()
                    + ", not the pinned NO_DEAL_FAILURE");
            }
            KindPayload.FieldWritePayload payload =
                (KindPayload.FieldWritePayload) op.payload();
            // The CLASS_FIELD_ASSIGNMENT descriptor is the field's
            // declared descriptor from the unit's local layout (the
            // lowerer produces class-field writes of locally declared
            // classes and of the compiler-owned builtin Error class).
            ClassLayout layout = unit.classLayouts().get(payload.classId());
            if (layout == null && ClassId.ERROR.equals(payload.classId())) {
                // The builtin Error field surface (ISSUE-0619; K13 items 3
                // and 4): the receiver resolves through the compiler-owned
                // builtin layout exactly like a locally declared class's —
                // the same layout entry every unit's context carries.
                layout = ClassLayout.BUILTIN_ERROR;
            }
            ClassLayout.FieldLayout fieldLayout = layout == null
                ? null : fieldOf(layout, payload.field());
            if (fieldLayout == null) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_WRITE " + op.opId()
                    + " of " + payload.classId() + "." + payload.field()
                    + " violates the pinned shape: the class must resolve in the unit's "
                    + "own classLayouts and the field must be a declared field (the "
                    + "CLASS_FIELD_ASSIGNMENT descriptor is the field's declared "
                    + "descriptor from the unit's local layout)");
            }
            List<SemanticOp> children = boundaryChildren(op);
            if (children.size() != 2) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_WRITE " + op.opId() + " parents "
                    + children.size() + " boundary children: the pinned shape is "
                    + "exactly [UNTYPED_CLASS_INPUT, CLASS_FIELD_ASSIGNMENT]");
            }
            String receiver = boundaryShapeViolation(children.get(0), op,
                BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor(payload.classId()),
                payload.classValue());
            if (receiver != null) {
                return fail(FIELD_OPERATION_SHAPE, receiver);
            }
            String field = boundaryShapeViolation(children.get(1), op,
                BoundaryKind.CLASS_FIELD_ASSIGNMENT, fieldLayout.descriptor(),
                payload.value());
            if (field != null) {
                return fail(FIELD_OPERATION_SHAPE, field);
            }
            return Optional.empty();
        }

        private Optional<CompilerDiagnostic> checkFieldDelete(SemanticOp op) {
            if (op.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_DELETE " + op.opId()
                    + " carries policy " + op.failurePolicy()
                    + ", not the pinned NO_DEAL_FAILURE");
            }
            KindPayload.FieldDeletePayload payload =
                (KindPayload.FieldDeletePayload) op.payload();
            List<SemanticOp> children = boundaryChildren(op);
            if (children.size() != 1) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_DELETE " + op.opId() + " parents "
                    + children.size() + " boundary children: the pinned shape is "
                    + "exactly [UNTYPED_CLASS_INPUT]");
            }
            String receiver = boundaryShapeViolation(children.get(0), op,
                BoundaryKind.UNTYPED_CLASS_INPUT, classDescriptor(payload.classId()),
                payload.classValue());
            if (receiver != null) {
                return fail(FIELD_OPERATION_SHAPE, receiver);
            }
            // When the layout resolves, a required-field delete is never
            // produced (checker E4004).
            ClassLayout layout = layoutContext.get(payload.classId());
            ClassLayout.FieldLayout fieldLayout = layout == null
                ? null : fieldOf(layout, payload.field());
            if (fieldLayout != null && fieldLayout.required()) {
                return fail(FIELD_OPERATION_SHAPE, "FIELD_DELETE " + op.opId()
                    + " deletes required field '" + payload.field() + "' of "
                    + payload.classId() + ": required-field deletes never reach the IR "
                    + "(checker E4004)");
            }
            return Optional.empty();
        }

        // =====================================================================
        // 4. DEFAULT_BLOCK_ADMISSION
        // =====================================================================

        Optional<CompilerDiagnostic> checkDefaultBlockAdmission() {
            // The producing block of every binding-producing allocation
            // kind (the B2 producing-allocation kinds): BINDING_ALLOC,
            // FOR_EACH (the iteration binding), RECURSIVE_GROUP_INIT (the
            // group members).
            Map<BindingId, BlockId> producingBlocks = new LinkedHashMap<>();
            for (SemanticOp op : unit.ops()) {
                switch (op.kind()) {
                    case BINDING_ALLOC -> {
                        KindPayload.BindingAllocPayload payload =
                            (KindPayload.BindingAllocPayload) op.payload();
                        BlockId block = table.opBlocks().get(op.opId());
                        if (block != null) {
                            producingBlocks.put(payload.binding(), block);
                        }
                    }
                    case FOR_EACH -> {
                        KindPayload.ForEachPayload payload =
                            (KindPayload.ForEachPayload) op.payload();
                        BlockId block = table.opBlocks().get(op.opId());
                        if (block != null) {
                            producingBlocks.put(payload.binding(), block);
                        }
                    }
                    case RECURSIVE_GROUP_INIT -> {
                        KindPayload.RecursiveGroupInitPayload payload =
                            (KindPayload.RecursiveGroupInitPayload) op.payload();
                        BlockId block = table.opBlocks().get(op.opId());
                        if (block != null) {
                            for (BindingId binding : payload.bindings()) {
                                producingBlocks.put(binding, block);
                            }
                        }
                    }
                    default -> {
                        // Not a binding producer.
                    }
                }
            }
            BlockId moduleInitBlock = unit.moduleInit().initBlock();
            for (SemanticOp op : unit.ops()) {
                if (op.kind() != SemanticOpKind.CLASS_DEFAULT) {
                    continue;
                }
                KindPayload.ClassDefaultPayload payload =
                    (KindPayload.ClassDefaultPayload) op.payload();
                if (!table.blockOps().containsKey(payload.defaultBlock())) {
                    return fail(DEFAULT_BLOCK_ADMISSION, "CLASS_DEFAULT " + op.opId()
                        + " of " + payload.classId() + "." + payload.field()
                        + " references block " + payload.defaultBlock() + " which is not "
                        + "a block of the membership table");
                }
                Set<BlockId> closure = defaultClosure(payload.defaultBlock());
                if (closure == null) {
                    return fail(DEFAULT_BLOCK_ADMISSION, "CLASS_DEFAULT " + op.opId()
                        + " of " + payload.classId() + "." + payload.field()
                        + " references a payload block outside the membership table");
                }
                Set<BlockId> admitted = new LinkedHashSet<>(closure);
                admitted.add(moduleInitBlock);
                for (SemanticOp member : unit.ops()) {
                    BlockId block = table.opBlocks().get(member.opId());
                    if (block == null || !closure.contains(block)) {
                        continue;
                    }
                    switch (member.kind()) {
                        case BINDING_LOAD -> {
                            KindPayload.BindingLoadPayload load =
                                (KindPayload.BindingLoadPayload) member.payload();
                            Optional<CompilerDiagnostic> failure = admitReference(op,
                                load.binding(), producingBlocks, admitted);
                            if (failure.isPresent()) {
                                return failure;
                            }
                        }
                        case CLOSURE_NEW -> {
                            KindPayload.ClosureNewPayload closurePayload =
                                (KindPayload.ClosureNewPayload) member.payload();
                            for (BindingId capture : closurePayload.captures()) {
                                Optional<CompilerDiagnostic> failure = admitReference(op,
                                    capture, producingBlocks, admitted);
                                if (failure.isPresent()) {
                                    return failure;
                                }
                            }
                        }
                        case FUNCTION_ADAPT -> {
                            KindPayload.FunctionAdaptPayload adaptPayload =
                                (KindPayload.FunctionAdaptPayload) member.payload();
                            if (adaptPayload.source()
                                    instanceof deal.semantic.ir.AdaptSourceRef.Thunk thunk) {
                                for (BindingGeneration capture
                                        : thunk.capturedBindings()) {
                                    Optional<CompilerDiagnostic> failure = admitReference(op,
                                        capture.binding(), producingBlocks, admitted);
                                    if (failure.isPresent()) {
                                        return failure;
                                    }
                                }
                            }
                        }
                        default -> {
                            // Other op kinds carry no binding references.
                        }
                    }
                }
            }
            return Optional.empty();
        }

        /** Admits one binding reference against the closed admission set. */
        private Optional<CompilerDiagnostic> admitReference(SemanticOp defaultOp,
                                                            BindingId binding,
                                                            Map<BindingId, BlockId>
                                                                producingBlocks,
                                                            Set<BlockId> admitted) {
            BlockId producing = producingBlocks.get(binding);
            if (producing == null || !admitted.contains(producing)) {
                return fail(DEFAULT_BLOCK_ADMISSION, "CLASS_DEFAULT " + defaultOp.opId()
                    + " of " + ((KindPayload.ClassDefaultPayload) defaultOp.payload())
                        .classId() + "." + ((KindPayload.ClassDefaultPayload)
                        defaultOp.payload()).field()
                    + " references binding " + binding + " whose producing allocation "
                    + (producing == null ? "is not a block member" : "sits in block "
                        + producing) + ": a default block admits only allocations inside "
                    + "the default closure itself and module-level bindings resolved "
                    + "through the module-init block (an enclosing-region free "
                    + "reference is invalid — K-D3)");
            }
            return Optional.empty();
        }

        /**
         * The block closure of one default block: the block itself plus
         * every block referenced by a payload position of an op whose
         * membership block is in the closure (a fixpoint over the
         * table). {@code null} when a referenced block is not a table
         * block.
         */
        private Set<BlockId> defaultClosure(BlockId root) {
            Set<BlockId> closure = new LinkedHashSet<>();
            closure.add(root);
            boolean extended = true;
            while (extended) {
                extended = false;
                for (SemanticOp op : unit.ops()) {
                    BlockId block = table.opBlocks().get(op.opId());
                    if (block == null || !closure.contains(block)) {
                        continue;
                    }
                    for (BlockId referenced : payloadBlocks(op.payload())) {
                        if (!table.blockOps().containsKey(referenced)) {
                            return null;
                        }
                        if (closure.add(referenced)) {
                            extended = true;
                        }
                    }
                }
            }
            return closure;
        }

        /** The block ids referenced by one payload's closed block positions. */
        private static List<BlockId> payloadBlocks(KindPayload payload) {
            List<BlockId> blocks = new ArrayList<>();
            switch (payload) {
                case KindPayload.ClassDefaultPayload p ->
                    blocks.add(p.defaultBlock());
                case KindPayload.BranchPayload p -> {
                    blocks.add(p.selectedBlock());
                    if (p.alternateBlock() != null) {
                        blocks.add(p.alternateBlock());
                    }
                }
                case KindPayload.LoopPayload p -> {
                    if (p.initBlock() != null) {
                        blocks.add(p.initBlock());
                    }
                    blocks.add(p.bodyBlock());
                    if (p.updateBlock() != null) {
                        blocks.add(p.updateBlock());
                    }
                }
                case KindPayload.ForEachPayload p -> blocks.add(p.body());
                case KindPayload.TryCatchPayload p -> {
                    blocks.add(p.tryBlock());
                    blocks.add(p.catchBlock());
                }
                case KindPayload.CallPayload p -> {
                    if (p.bodyBlock() != null) {
                        blocks.add(p.bodyBlock());
                    }
                }
                case KindPayload.BindingAllocPayload p -> blocks.add(p.scope());
                case KindPayload.FunctionAdaptPayload p -> {
                    if (p.source() instanceof deal.semantic.ir.AdaptSourceRef.Thunk thunk) {
                        blocks.add(thunk.blockId());
                    }
                }
                case KindPayload.ClosureNewPayload p -> blocks.add(p.binding().blockId());
                default -> {
                    // No block position.
                }
            }
            return blocks;
        }

        // =====================================================================
        // 5. JSON_LAYOUT_COHERENCE
        // =====================================================================

        Optional<CompilerDiagnostic> checkJsonLayoutCoherence() {
            for (SemanticOp op : unit.ops()) {
                switch (op.kind()) {
                    case JSON_FROM_CLASS -> {
                        Optional<CompilerDiagnostic> failure = checkJsonFromClass(op);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                    case JSON_TO_CLASS -> {
                        Optional<CompilerDiagnostic> failure = checkJsonToClass(op);
                        if (failure.isPresent()) {
                            return failure;
                        }
                    }
                    default -> {
                        // Not a JSON op.
                    }
                }
            }
            // No orphan JsonDefaultChildTable entries: every key is a
            // produced JSON_FROM_CLASS op.
            for (OpId key : jsonDefaults.defaultChildren().keySet()) {
                SemanticOp op = op(key);
                if (op == null || op.kind() != SemanticOpKind.JSON_FROM_CLASS) {
                    return fail(JSON_LAYOUT_COHERENCE, "the JsonDefaultChildTable "
                        + "records a default-child entry for " + key + " which is not "
                        + "a produced JSON_FROM_CLASS op of the unit");
                }
            }
            return Optional.empty();
        }

        /** The shared JSON-op preamble: policy and the unit's own layout. */
        private ClassLayout jsonOpLayout(SemanticOp op, FailurePolicyId pinnedPolicy,
                                         ClassLayout payloadLayout) {
            if (op.failurePolicy() != pinnedPolicy) {
                return null;
            }
            ClassLayout ownLayout = unit.classLayouts().get(payloadLayout.classId());
            if (ownLayout == null || !ownLayout.equals(payloadLayout)) {
                return null;
            }
            return ownLayout;
        }

        private Optional<CompilerDiagnostic> checkJsonFromClass(SemanticOp op) {
            KindPayload.JsonFromClassPayload payload =
                (KindPayload.JsonFromClassPayload) op.payload();
            ClassLayout layout = jsonOpLayout(op, FailurePolicyId.JSON_FROM_NULL,
                payload.layout());
            if (layout == null) {
                return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                    + " violates the pinned shape: policy must be JSON_FROM_NULL and "
                    + "the payload layout must be exactly the unit's own layout of "
                    + payload.layout().classId());
            }
            // The per-site default children: exactly the class's
            // required-present defaulted fields' CLASS_DEFAULT op ids in
            // declaration order.
            List<String> expected = new ArrayList<>();
            for (ClassLayout.FieldLayout field : layout.fields()) {
                if (field.required() && defaultOp(layout.classId(), field.name())
                        != null) {
                    expected.add(field.name());
                }
            }
            List<OpId> children = jsonDefaults.childrenOf(op.opId());
            if (children == null) {
                children = List.of();
            }
            if (children.size() != expected.size()) {
                return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                    + " records " + children.size() + " per-site CLASS_DEFAULT "
                    + "children for " + expected.size() + " required-present defaulted "
                    + "fields: the pinned table entry lists exactly those fields' op "
                    + "ids in declaration order");
            }
            for (int i = 0; i < expected.size(); i++) {
                SemanticOp child = op(children.get(i));
                if (child == null) {
                    return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                        + " lists CLASS_DEFAULT child " + children.get(i) + " (field '"
                        + expected.get(i) + "') which is not a produced op of the unit");
                }
                if (child.kind() != SemanticOpKind.CLASS_DEFAULT) {
                    return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                        + " lists child " + children.get(i) + " of kind " + child.kind()
                        + " for field '" + expected.get(i) + "', not CLASS_DEFAULT");
                }
                KindPayload.ClassDefaultPayload childPayload =
                    (KindPayload.ClassDefaultPayload) child.payload();
                if (!childPayload.classId().equals(layout.classId())
                        || !childPayload.field().equals(expected.get(i))) {
                    return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                        + " lists child " + children.get(i) + " for "
                        + childPayload.classId() + "." + childPayload.field() + ", not "
                        + layout.classId() + "." + expected.get(i));
                }
                if (child.failurePolicy() != FailurePolicyId.NO_DEAL_FAILURE) {
                    return fail(JSON_LAYOUT_COHERENCE, "JSON_FROM_CLASS " + op.opId()
                        + " lists CLASS_DEFAULT child " + children.get(i) + " carrying "
                        + "policy " + child.failurePolicy() + ", not NO_DEAL_FAILURE");
                }
            }
            return checkNestedJsonable(layout, new LinkedHashSet<>());
        }

        private Optional<CompilerDiagnostic> checkJsonToClass(SemanticOp op) {
            KindPayload.JsonToClassPayload payload =
                (KindPayload.JsonToClassPayload) op.payload();
            ClassLayout layout = jsonOpLayout(op, FailurePolicyId.JSON_TO_ERROR,
                payload.layout());
            if (layout == null) {
                return fail(JSON_LAYOUT_COHERENCE, "JSON_TO_CLASS " + op.opId()
                    + " violates the pinned shape: policy must be JSON_TO_ERROR and "
                    + "the payload layout must be exactly the unit's own layout of "
                    + payload.layout().classId());
            }
            return checkNestedJsonable(layout, new LinkedHashSet<>());
        }

        /**
         * The nested-jsonable layout/factory resolvability of one
         * jsonable layout (K-D8 step 6/K-D10 recursion): every
         * class-typed field resolves to a layout in the context and —
         * for imported classes — to the {@link SharedFactoryFacts}
         * context; an own exported nested class's constructionEntry
         * must be registered (the JSON nested-factory trigger). Bytes
         * and function-typed fields are checker-rejected (E4007) and
         * fail closed here.
         */
        private Optional<CompilerDiagnostic> checkNestedJsonable(ClassLayout layout,
                                                                 Set<ClassId> visited) {
            if (!visited.add(layout.classId())) {
                // A visited layout is the checker-rejected same-module
                // jsonable cycle (E4008); the recursion guard never
                // silently admits a cycle, but re-entry with a pinned
                // layout set is tolerated for robustness of the pure
                // walk. (The checker's E4008 gate makes a produced cycle
                // unreachable.)
                return Optional.empty();
            }
            for (ClassLayout.FieldLayout field : layout.fields()) {
                Optional<CompilerDiagnostic> failure = checkJsonableDescriptor(
                    layout.classId(), field.name(), field.descriptor(), visited);
                if (failure.isPresent()) {
                    return failure;
                }
            }
            return Optional.empty();
        }

        private Optional<CompilerDiagnostic> checkJsonableDescriptor(ClassId owner,
                                                                     String field,
                                                                     RuntimeDescriptor
                                                                         descriptor,
                                                                     Set<ClassId> visited) {
            return switch (descriptor) {
                case RuntimeDescriptor.Null ignored -> Optional.empty();
                case RuntimeDescriptor.Boolean ignored -> Optional.empty();
                case RuntimeDescriptor.Int ignored -> Optional.empty();
                case RuntimeDescriptor.Number ignored -> Optional.empty();
                case RuntimeDescriptor.String ignored -> Optional.empty();
                case RuntimeDescriptor.Table ignored -> Optional.empty();
                case RuntimeDescriptor.Array array -> checkJsonableDescriptor(owner,
                    field, array.element(), visited);
                case RuntimeDescriptor.Nullable nullable ->
                    checkJsonableDescriptor(owner, field, nullable.inner(), visited);
                case RuntimeDescriptor.Class classDescriptor -> {
                    ClassId nested = classDescriptor.classId();
                    ClassLayout nestedLayout = layoutContext.get(nested);
                    if (nestedLayout == null) {
                        yield fail(JSON_LAYOUT_COHERENCE, "jsonable class " + owner
                            + " field '" + field + "' references nested class " + nested
                            + " which does not resolve in the layout context (the "
                            + "unit's classLayouts plus the imported classes' "
                            + "layouts)");
                    }
                    if (unit.classLayouts().containsKey(nested)) {
                        // An own nested class: its layout is the unit's.
                        if (!unit.classLayouts().get(nested).equals(nestedLayout)) {
                            yield fail(JSON_LAYOUT_COHERENCE, "jsonable class " + owner
                                + " field '" + field + "' nested class " + nested
                                + " resolves to a layout that differs from the unit's "
                                + "own layout");
                        }
                        ClassInterface ownEntry = interfaceContext.get(nested);
                        if (ownEntry != null) {
                            // An own exported nested class: the JSON nested
                            // decode triggers its CLASS_FACTORY (K-D8 step
                            // 6), so the constructionEntry must be
                            // registered.
                            if (factories.factoryFor(ownEntry.constructionEntry())
                                    == null) {
                                yield fail(JSON_LAYOUT_COHERENCE, "jsonable class "
                                    + owner + " field '" + field + "' nested class "
                                    + nested + " is exported but has no registered "
                                    + "factory under its constructionEntry: the nested "
                                    + "JSON decode triggers the nested CLASS_FACTORY");
                            }
                        }
                        yield checkNestedJsonable(nestedLayout, visited);
                    }
                    // An imported nested class: the SharedFactoryFacts
                    // context must carry its interface entry and layout
                    // (the nested decode resolves the owner factory
                    // through the project's factory registries).
                    SharedFactoryFacts facts = factsOf(nested);
                    if (facts == null) {
                        yield fail(JSON_LAYOUT_COHERENCE, "jsonable class " + owner
                            + " field '" + field + "' references imported nested class "
                            + nested + " without shared-factory facts: the "
                            + "SharedFactoryFacts context must cover every imported "
                            + "class the unit's class constructs reference");
                    }
                    if (!facts.layout().equals(nestedLayout)) {
                        yield fail(JSON_LAYOUT_COHERENCE, "jsonable class " + owner
                            + " field '" + field + "' nested class " + nested
                            + " resolves to a layout that differs from the imported "
                            + "facts' layout");
                    }
                    yield checkNestedJsonable(nestedLayout, visited);
                }
                case RuntimeDescriptor.Bytes ignored -> fail(JSON_LAYOUT_COHERENCE,
                    "jsonable class " + owner + " field '" + field + "' carries a "
                        + "bytes descriptor: the checker's E4007 allowlist excludes "
                        + "bytes-typed jsonable fields");
                case RuntimeDescriptor.Func ignored -> fail(JSON_LAYOUT_COHERENCE,
                    "jsonable class " + owner + " field '" + field + "' carries a "
                        + "function descriptor: the checker's E4007 allowlist excludes "
                        + "function-typed jsonable fields");
            };
        }
    }
}
