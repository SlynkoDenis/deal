package deal.test;

import deal.semantic.ir.AdaptSourceRef;
import deal.semantic.ir.AnchorId;
import deal.semantic.ir.AssignTargetKind;
import deal.semantic.ir.AsyncLinkKind;
import deal.semantic.ir.AsyncStartSource;
import deal.semantic.ir.AsyncTokenId;
import deal.semantic.ir.AsyncTokenOwner;
import deal.semantic.ir.BindingCellKind;
import deal.semantic.ir.BindingGeneration;
import deal.semantic.ir.BindingId;
import deal.semantic.ir.BindingImmutabilityProof;
import deal.semantic.ir.BinarySelector;
import deal.semantic.ir.BlockId;
import deal.semantic.ir.BoundaryKind;
import deal.semantic.ir.BoundaryRealization;
import deal.semantic.ir.CallMode;
import deal.semantic.ir.CapabilityRequirementCatalog;
import deal.semantic.ir.CaptureMode;
import deal.semantic.ir.ClassFactoryId;
import deal.semantic.ir.ClassId;
import deal.semantic.ir.ClassInterface;
import deal.semantic.ir.ClassLayout;
import deal.semantic.ir.ClosedSelector;
import deal.semantic.ir.ConstructKind;
import deal.semantic.ir.ControlSelector;
import deal.semantic.ir.DefaultOwner;
import deal.semantic.ir.DeleteTargetKind;
import deal.semantic.ir.ExecutableLoweredProject;
import deal.semantic.ir.ExportInterface;
import deal.semantic.ir.ExportPlan;
import deal.semantic.ir.ExternalAsyncLink;
import deal.semantic.ir.ExternalExecutionOwner;
import deal.semantic.ir.ExternalModuleInterface;
import deal.semantic.ir.ExternalModuleKind;
import deal.semantic.ir.FailurePolicyId;
import deal.semantic.ir.FieldInterface;
import deal.semantic.ir.FunctionAllocationIdentity;
import deal.semantic.ir.FunctionExecutionBinding;
import deal.semantic.ir.FunctionId;
import deal.semantic.ir.ResolvedImport;
import deal.semantic.ir.InitializationMode;
import deal.semantic.ir.InternalResultType;
import deal.semantic.ir.IntrinsicKind;
import deal.semantic.ir.IndexMode;
import deal.semantic.ir.OpResultType;
import deal.semantic.ir.InvocationPurpose;
import deal.semantic.ir.IterationMode;
import deal.semantic.ir.KindPayload;
import deal.semantic.ir.LoweredFunction;
import deal.semantic.ir.LoweredModuleUnit;
import deal.semantic.ir.LoweringContext;
import deal.semantic.ir.ModuleId;
import deal.semantic.ir.ModuleImportKind;
import deal.semantic.ir.ModuleInitPlan;
import deal.semantic.ir.NullableSide;
import deal.semantic.ir.OpId;
import deal.semantic.ir.OperationContractSnapshot;
import deal.semantic.ir.ParameterBoundaryMode;
import deal.semantic.ir.ProjectInterfaceIndex;
import deal.semantic.ir.ReleaseState;
import deal.semantic.ir.RuntimeDescriptor;
import deal.semantic.ir.ScalarValue;
import deal.semantic.ir.SemanticCapability;
import deal.semantic.ir.SemanticId;
import deal.semantic.ir.SemanticOp;
import deal.semantic.ir.SemanticOpKind;
import deal.semantic.ir.SemanticProfile;
import deal.semantic.ir.SemanticValue;
import deal.semantic.ir.SourceOrigin;
import deal.semantic.ir.SourceOriginKind;
import deal.semantic.ir.SourceSpan;
import deal.semantic.ir.StdlibFunctionId;
import deal.semantic.ir.UnarySelector;
import deal.semantic.ir.ValueId;

import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Verifies the ISSUE-0282 closed {@code deal.semantic-ir/1} schema core:
 * record shapes, semantic ID types, {@link RuntimeDescriptor} canonical
 * spec text, the closed enums and reserved names, the 55 per-kind payload
 * shapes, the capability catalog, and the 23-row source-construct coverage
 * table — as pure immutable data in {@code deal.semantic.ir} consuming
 * nothing from {@code deal.ast}/{@code deal.checker}/{@code deal.codegen}/
 * {@code deal.module}.
 *
 * <p>Tests:
 * <ol>
 *   <li>Exhaustive closed-enum enumeration: every closed enum's value list
 *       equals the verbatim design list (names + order + counts: 55 kinds,
 *       3 unary, 42 binary, 4 call modes, 3 async sources, 2 parameter
 *       boundary modes, 4 index modes, 2 iteration modes, 6 control
 *       selectors, 3 capture modes, 25 boundary kinds, 24 policies, 21
 *       stdlib ids); reserved names marked invalid.</li>
 *   <li>Reflective closedness: the reserved names have no enum member
 *       anywhere in {@code deal.semantic.ir} ({@code TIME_NOW_MILLIS} is a
 *       member of exactly {@link StdlibFunctionId}; the four reserved
 *       policy names absent from every enum except {@link BoundaryKind};
 *       the three reserved boundary names absent from every enum), and no
 *       constructor path admits a {@code semanticProfile} other than
 *       {@code DEAL_V1_2_INT32}.</li>
 *   <li>The closed 23-row source-construct table: verbatim required common
 *       forms for all 23 rows (no row is excluded since K7:
 *       {@code STDLIB_TIME_NOW_MILLIS} carries its form and op-kind set
 *       and is admitted as a {@code constructCoverage} key).</li>
 *   <li>Payload construction: every {@link SemanticOpKind} maps to exactly
 *       one {@link KindPayload} record shape and a minimal instance is
 *       constructible; missing mandatory payload fields are rejected
 *       ({@code CALL} without {@code CallMode}, {@code BOUNDARY} without
 *       realization, {@code CLASS_NEW} without {@code defaultOwner} cannot
 *       be constructed).</li>
 *   <li>{@link RuntimeDescriptor} canonical spec text goldens for every
 *       variant incl. signed32 int and sync/async function forms.</li>
 *   <li>{@link CapabilityRequirementCatalog} keyed by T1's closed
 *       {@link SemanticCapability} enum; the synthetic-unit integration
 *       builds a unit requiring {@code FOUNDATION_VALUES} +
 *       {@code SIGNED_INT32}.</li>
 *   <li>{@link SemanticOp}/{@link OperationContractSnapshot} wiring and
 *       the {@link LoweredModuleUnit}/{@link ExecutableLoweredProject}
 *       pinned constraints.</li>
 *   <li>Package hygiene: {@code deal.semantic.ir} imports nothing outside
 *       the JDK (no {@code deal.ast}/{@code deal.checker}/
 *       {@code deal.codegen}/{@code deal.module} … imports anywhere in the
 *       package).</li>
 * </ol>
 */
public class SemanticIrSchemaTest {

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

    private static void expectRejected(Runnable construction, String message) {
        try {
            construction.run();
            fail(message + " (no exception thrown)");
        } catch (RuntimeException expected) {
            check(true, message + " (rejected with " + expected.getClass().getSimpleName()
                + ": " + expected.getMessage() + ")");
        }
    }

    // =========================================================================
    // Closed enums: verbatim value lists (names + order + counts)
    // =========================================================================

    private static final List<String> OP_KINDS = List.of(
        "CONST", "UNARY", "BINARY", "STRING_CONCAT", "ARRAY_NEW", "TABLE_NEW",
        "ARRAY_LENGTH", "MEMBER_READ", "MEMBER_WRITE", "MEMBER_DELETE",
        "INDEX_NORMALIZE", "INDEX_READ", "INDEX_WRITE", "INDEX_DELETE",
        "OPTIONAL_READ", "HAS_FIELD", "BOUNDARY", "BINDING_ALLOC", "BINDING_INIT",
        "BINDING_LOAD", "BINDING_STORE", "RECURSIVE_GROUP_INIT", "CLOSURE_NEW",
        "FUNCTION_ADAPT", "ASSIGN", "DELETE", "CALL", "EXTERNAL_ENTRY",
        "CALLBACK_INVOKE", "INTRINSIC_CALL", "STDLIB_CALL", "ASYNC_START", "AWAIT",
        "BRANCH", "LOOP", "FOR_EACH", "TRY_CATCH", "THROW", "RETURN", "BREAK",
        "CONTINUE", "DISCARD", "CLASS_DEFAULT", "CLASS_NEW", "CLASS_FACTORY",
        "FIELD_READ", "FIELD_WRITE", "FIELD_DELETE", "JSON_FROM_CLASS",
        "JSON_TO_CLASS", "MODULE_INIT", "MODULE_IMPORT", "EXPORT_READ",
        "EXPORT_PUBLISH", "ENTRY_INVOKE");

    private static final List<String> UNARY_SELECTORS =
        List.of("BOOL_NOT", "INT32_NEG", "NUMBER_NEG");

    private static final List<String> BINARY_SELECTORS = List.of(
        "INT32_ADD", "INT32_SUB", "INT32_MUL", "INT32_DIV_TRUNC", "INT32_MOD_TRUNC",
        "INT32_POW", "NUMBER_ADD", "NUMBER_SUB", "NUMBER_MUL", "NUMBER_DIV_IEEE",
        "NUMBER_MOD_FLOOR", "NUMBER_POW_IEEE", "INT32_EQ", "INT32_NE", "INT32_LT",
        "INT32_LE", "INT32_GT", "INT32_GE", "NUMBER_EQ", "NUMBER_NE", "NUMBER_LT",
        "NUMBER_LE", "NUMBER_GT", "NUMBER_GE", "STRING_EQ", "STRING_NE", "STRING_LT",
        "STRING_LE", "STRING_GT", "STRING_GE", "BOOLEAN_EQ", "BOOLEAN_NE", "NULL_EQ",
        "NULL_NE", "NULLABLE_EQ", "NULLABLE_NE", "NULLABLE_NULL_EQ",
        "NULLABLE_NULL_NE", "REFERENCE_EQ", "REFERENCE_NE", "BYTES_EQ",
        "BYTES_NE");

    private static final List<String> BOUNDARY_KINDS = List.of(
        "VARIABLE_DECLARATION", "VARIABLE_ASSIGNMENT", "CLASS_FIELD_ASSIGNMENT",
        "ARRAY_ELEMENT_ASSIGNMENT", "BYTE_ELEMENT_ASSIGNMENT", "ARRAY_ELEMENT_READ",
        "BYTE_ELEMENT_READ", "ARRAY_ELEMENT_DELETE",
        "ARRAY_LITERAL_ELEMENT", "FUNCTION_PARAMETER", "FUNCTION_RETURN",
        "ASYNC_COMPLETION", "CLASS_LITERAL_FIELD", "CLASS_DEFAULT_FIELD",
        "UNTYPED_CLASS_INPUT", "OPTIONAL_FIELD_READ", "CONTEXTUAL_TABLE_READ",
        "IMPORTED_MEMBER_READ", "MODULE_EXPORT", "HOST_TO_DEAL", "DEAL_TO_HOST",
        "STDLIB_PARAMETER", "STDLIB_RETURN", "EXTERNAL_PARAMETER", "EXTERNAL_RETURN",
        "JSON_FROM_FIELD", "JSON_TO_FIELD");

    private static final List<String> FAILURE_POLICIES = List.of(
        "NO_DEAL_FAILURE", "TYPE_DESCRIPTOR", "INT32_RESULT",
        "INT32_DIVISOR_THEN_RESULT", "INT32_EXPONENT_THEN_RESULT", "INT_CONVERSION",
        "NUMBER_CONVERSION", "ARRAY_ELEMENT_DESCRIPTOR",
        "ARRAY_READ_INDEX_THEN_DESCRIPTOR", "ARRAY_WRITE_BOUNDS_THEN_ELEMENT",
        "ARRAY_DELETE_BOUNDS", "BYTES_ALLOCATE", "BYTES_READ", "BYTES_WRITE",
        "FUNCTION_SIGNATURE", "HOST_PARAMETER",
        "HOST_SYNC_RETURN", "ASYNC_COMPLETION", "ASYNC_OPERATION_HANDLE",
        "HOST_LOAD", "CLASS_CONSTRUCTION", "JSON_PARSE_SYNTAX", "JSON_FROM_NULL",
        "JSON_TO_ERROR", "SQRT_NEGATIVE", "THROW_TRANSFER", "INFRASTRUCTURE_ONLY");

    private static final List<String> STDLIB_IDS = List.of(
        "CONSOLE_LOG", "CONSOLE_ERROR", "STRING_LENGTH", "STRING_SUBSTRING",
        "STRING_CONTAINS", "STRING_STARTS_WITH", "STRING_ENDS_WITH",
        "STRING_REPLACE", "STRING_SPLIT", "STRING_TRIM", "TABLE_KEYS", "JSON_PARSE",
        "JSON_STRINGIFY", "MATH_FLOOR", "MATH_CEIL", "MATH_SQRT", "MATH_ABS_INT",
        "MATH_ABS_NUMBER", "MATH_MIN_INT", "MATH_MAX_INT", "TIME_NOW_MILLIS");

    static void testClosedEnum(Class<? extends Enum<?>> type, List<String> pinned, String name) {
        System.out.println("-- Closed enum " + name + " --");
        check(type.isEnum(), name + " is an enum type");
        Enum<?>[] constants = type.getEnumConstants();
        List<String> actual = new ArrayList<>();
        for (Enum<?> c : constants) {
            actual.add(c.name());
        }
        check(actual.equals(pinned),
            name + " contains exactly " + pinned + " in the pinned order; got " + actual);
        check(constants.length == pinned.size(),
            name + " has exactly " + pinned.size() + " constants (no extra members)");
        for (Enum<?> c : constants) {
            String n = c.name();
            check(!n.equals("UNKNOWN") && !n.equals("OPEN") && !n.equals("OTHER")
                    && !n.equals("UNSPECIFIED") && !n.equals("CUSTOM"),
                name + " has no open/unknown fallback member (offending: " + n + ")");
        }
    }

    static void testClosedEnums() {
        testClosedEnum(SemanticOpKind.class, OP_KINDS, "SemanticOpKind");
        testClosedEnum(UnarySelector.class, UNARY_SELECTORS, "UnarySelector");
        testClosedEnum(BinarySelector.class, BINARY_SELECTORS, "BinarySelector");
        testClosedEnum(CallMode.class, List.of("DIRECT", "INDIRECT", "HOST", "EXTERNAL"),
            "CallMode");
        testClosedEnum(AsyncStartSource.class, List.of("DEAL_BODY", "HOST", "EXTERNAL"),
            "AsyncStartSource");
        testClosedEnum(ParameterBoundaryMode.class, List.of("RUN", "ELIDED_BY_ADAPTER"),
            "ParameterBoundaryMode");
        testClosedEnum(IndexMode.class,
            List.of("ARRAY_READ", "ARRAY_WRITE", "BYTES_READ", "BYTES_WRITE", "TABLE_READ",
                "TABLE_WRITE"), "IndexMode");
        testClosedEnum(IterationMode.class, List.of("ARRAY_VALUES", "STRING_SCALARS"),
            "IterationMode");
        testClosedEnum(ControlSelector.class, List.of("IF", "LOGICAL_AND", "LOGICAL_OR",
            "WHILE", "FOR", "TRY_CATCH"), "ControlSelector");
        testClosedEnum(CaptureMode.class, List.of("VALUE", "SHARED_CELL", "REEVALUATE_THUNK"),
            "CaptureMode");
        testClosedEnum(BoundaryKind.class, BOUNDARY_KINDS, "BoundaryKind");
        testClosedEnum(FailurePolicyId.class, FAILURE_POLICIES, "FailurePolicyId");
        testClosedEnum(StdlibFunctionId.class, STDLIB_IDS, "StdlibFunctionId");
        testClosedEnum(SourceOriginKind.class, List.of("USER", "SYNTHETIC"),
            "SourceOriginKind");
        testClosedEnum(AsyncTokenOwner.class, List.of("DEAL_BODY_TASK", "HOST_OPERATION"),
            "AsyncTokenOwner");
        testClosedEnum(AsyncLinkKind.class, List.of("EXTERNAL_LINK", "ADAPTER_INNER"),
            "AsyncLinkKind");
        testClosedEnum(NullableSide.class, List.of("LEFT", "RIGHT", "BOTH"), "NullableSide");
        testClosedEnum(IntrinsicKind.class,
            List.of("INT_CONVERT", "NUMBER_CONVERT", "BYTES_NEW"), "IntrinsicKind");
        testClosedEnum(BindingCellKind.class, List.of("DIRECT", "SHARED_CELL"),
            "BindingCellKind");
        testClosedEnum(AssignTargetKind.class,
            List.of("VARIABLE", "TABLE_SLOT", "ARRAY_SLOT", "BYTES_SLOT", "CLASS_FIELD"),
            "AssignTargetKind");
        testClosedEnum(DeleteTargetKind.class, List.of("TABLE_SLOT", "ARRAY_SLOT", "CLASS_FIELD"),
            "DeleteTargetKind");
        testClosedEnum(DefaultOwner.class, List.of("LOCAL", "SHARED_FACTORY", "RETAINED_ABI",
            "HOST_DEFAULTS", "FFI_PLAN", "BUILTIN_DEFAULTS"),
            "DefaultOwner");
        testClosedEnum(ExternalExecutionOwner.class, List.of("SHARED_BODY", "RETAINED_ABI"),
            "ExternalExecutionOwner");
        testClosedEnum(deal.semantic.ir.DynamicResolutionKind.class,
            List.of("DEAL_BODY", "HOST", "EXTERNAL", "SHARED_BODY"),
            "DynamicResolutionKind");
        testClosedEnum(ModuleImportKind.class, List.of("COMPILED", "STDLIB", "HOST"),
            "ModuleImportKind");
        testClosedEnum(ExternalModuleKind.class,
            List.of("IMPLEMENTATION", "DECLARATION", "STDLIB", "HOST"), "ExternalModuleKind");
        testClosedEnum(InitializationMode.class, List.of("ONCE_AFTER_DEPENDENCIES"),
            "InitializationMode");
        testClosedEnum(InternalResultType.class, List.of("INTERNAL_MISSING", "INTERNAL_ASYNC"),
            "InternalResultType");

        // Pinned counts asserted verbatim (names + order + counts).
        check(OP_KINDS.size() == 55, "SemanticOpKind has exactly 55 values; got " + OP_KINDS.size());
        check(UNARY_SELECTORS.size() == 3, "UnarySelector has exactly 3 values");
        check(BINARY_SELECTORS.size() == 42, "BinarySelector has exactly 42 values; got " + BINARY_SELECTORS.size());
        check(BOUNDARY_KINDS.size() == 27, "BoundaryKind has exactly 27 values; got " + BOUNDARY_KINDS.size());
        check(FAILURE_POLICIES.size() == 27, "FailurePolicyId has exactly 27 values; got " + FAILURE_POLICIES.size());
        check(STDLIB_IDS.size() == 21, "StdlibFunctionId has exactly 21 values; got " + STDLIB_IDS.size());
    }

    // =========================================================================
    // Reserved names: marked invalid, no enum member anywhere in deal.semantic.ir
    // =========================================================================

    static List<Class<? extends Enum<?>>> allEnumsInPackage() {
        List<Class<? extends Enum<?>>> result = new ArrayList<>();
        List<Class<?>> all = List.of(
            SemanticOpKind.class, UnarySelector.class, BinarySelector.class, CallMode.class,
            AsyncStartSource.class, ParameterBoundaryMode.class, IndexMode.class,
            IterationMode.class, ControlSelector.class, CaptureMode.class, BoundaryKind.class,
            FailurePolicyId.class, StdlibFunctionId.class, SourceOriginKind.class,
            AsyncTokenOwner.class, AsyncLinkKind.class, NullableSide.class, IntrinsicKind.class,
            BindingCellKind.class, AssignTargetKind.class, DeleteTargetKind.class,
            DefaultOwner.class, ExternalExecutionOwner.class, ModuleImportKind.class,
            ExternalModuleKind.class, InitializationMode.class, InternalResultType.class,
            deal.semantic.ir.DynamicResolutionKind.class,
            SemanticProfile.class, InvocationPurpose.class, ReleaseState.class,
            SemanticCapability.class, ConstructKind.class);
        for (Class<?> c : all) {
            if (c.isEnum()) {
                @SuppressWarnings("unchecked")
                Class<? extends Enum<?>> e = (Class<? extends Enum<?>>) c;
                result.add(e);
            }
        }
        return result;
    }

    static boolean enumHasMember(List<Class<? extends Enum<?>>> enums, String name) {
        for (Class<? extends Enum<?>> e : enums) {
            for (Enum<?> c : e.getEnumConstants()) {
                if (c.name().equals(name)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static Class<? extends Enum<?>> enumMemberOf(List<Class<? extends Enum<?>>> enums,
                                                         String name) {
        Class<? extends Enum<?>> found = null;
        for (Class<? extends Enum<?>> e : enums) {
            for (Enum<?> c : e.getEnumConstants()) {
                if (c.name().equals(name)) {
                    if (found != null && found != e) {
                        return null; // ambiguous: more than one enum carries the name
                    }
                    found = e;
                }
            }
        }
        return found;
    }

    static void testReservedNames() {
        System.out.println("-- Reserved names marked invalid --");

        check(BoundaryKind.RESERVED_NAMES.equals(
                List.of("C_FFI_TO_DEAL", "DEAL_TO_C_FFI")),
            "BoundaryKind.RESERVED_NAMES is exactly the two reserved boundary names");
        check(FailurePolicyId.RESERVED_NAMES.equals(
                List.of("EXTERNAL_PARAMETER", "EXTERNAL_RETURN", "STDLIB_PARAMETER", "STDLIB_RETURN")),
            "FailurePolicyId.RESERVED_NAMES is exactly the four reserved policy names");
        check(StdlibFunctionId.RESERVED_NAMES.isEmpty(),
            "StdlibFunctionId.RESERVED_NAMES is empty (TIME_NOW_MILLIS is the 21st member "
                + "since K7; the reserved-name guard stays as the closed-set machinery)");

        for (String name : BoundaryKind.RESERVED_NAMES) {
            check(BoundaryKind.isReservedName(name), name + " is marked invalid as a boundary kind");
        }
        for (String name : FailurePolicyId.RESERVED_NAMES) {
            check(FailurePolicyId.isReservedName(name), name + " is marked invalid as a failure policy");
        }
        check(!StdlibFunctionId.isReservedName("TIME_NOW_MILLIS")
                && !StdlibFunctionId.isReservedName("ANY_OTHER_NAME"),
            "TIME_NOW_MILLIS is a closed stdlib selector member, never a reserved name "
                + "(the empty reservation list denies every name by default)");

        // Reflective closedness over every enum in deal.semantic.ir.
        List<Class<? extends Enum<?>>> enums = allEnumsInPackage();
        check(enumHasMember(enums, "TIME_NOW_MILLIS")
                && enumMemberOf(enums, "TIME_NOW_MILLIS") == StdlibFunctionId.class,
            "TIME_NOW_MILLIS is a member of exactly the closed StdlibFunctionId enum");
        for (String name : FailurePolicyId.RESERVED_NAMES) {
            // The four names are valid BoundaryKind values and invalid
            // FailurePolicyId values — and no other enum may carry them.
            boolean inBoundary = BoundaryKind.valueOf(name) != null;
            for (Class<? extends Enum<?>> e : enums) {
                if (e == BoundaryKind.class) {
                    continue;
                }
                for (Enum<?> c : e.getEnumConstants()) {
                    check(!c.name().equals(name),
                        name + " must not be a member of " + e.getSimpleName()
                            + " (reserved FailurePolicyId; valid BoundaryKind only)");
                }
            }
            check(inBoundary, name + " remains a valid BoundaryKind value");
        }
        for (String name : BoundaryKind.RESERVED_NAMES) {
            check(!enumHasMember(enums, name),
                name + " is not a member of any enum in deal.semantic.ir");
        }
        // The policy-reserved names are not members of FailurePolicyId itself.
        for (String name : FailurePolicyId.RESERVED_NAMES) {
            boolean member = false;
            for (FailurePolicyId p : FailurePolicyId.values()) {
                if (p.name().equals(name)) {
                    member = true;
                }
            }
            check(!member, name + " is not a member of FailurePolicyId");
        }
    }

    // =========================================================================
    // Source-construct coverage table: exactly 23 verbatim rows
    // =========================================================================

    static void testConstructTable() {
        System.out.println("-- Source-construct coverage table (23 rows) --");

        ConstructKind[] kinds = ConstructKind.values();
        check(kinds.length == 23, "ConstructKind has exactly 23 rows; got " + kinds.length);

        Map<String, String> pinned = new LinkedHashMap<>();
        pinned.put("SCALAR_LITERAL", "CONST");
        pinned.put("IDENTIFIER",
            "BINDING_LOAD, intrinsic binding, or explicit import/export reference");
        pinned.put("UNARY_ARITHMETIC_COMPARISON",
            "UNARY/BINARY; logical operators use selector-bearing BRANCH");
        pinned.put("STRING_CONCAT_TEMPLATE",
            "STRING_CONCAT with every fragment/interpolation in source order");
        pinned.put("CALL", "CALL (DIRECT/INDIRECT with execution-binding resolution), CALLBACK_INVOKE, "
            + "INTRINSIC_CALL, STDLIB_CALL, or ASYNC_START+AWAIT");
        pinned.put("CROSS_MODULE_CALL", "CALL(EXTERNAL)/ASYNC_START(EXTERNAL) with EXTERNAL_ENTRY on the "
            + "shared-body callee side, or the retained ABI path");
        pinned.put("MEMBER_ACCESS",
            "ARRAY_LENGTH, FIELD_READ, MEMBER_READ, or EXPORT_READ from checked type/symbol");
        pinned.put("INDEX_ACCESS",
            "INDEX_NORMALIZE, INDEX_READ (ARRAY_ELEMENT_READ boundary), contextual BOUNDARY");
        pinned.put("ARRAY_OBJECT_LITERAL", "ARRAY_NEW (ARRAY_LITERAL_ELEMENT boundaries), TABLE_NEW");
        pinned.put("CLASS_OBJECT_LITERAL", "CLASS_NEW (local and imported); imported defaults via the owner's "
            + "CLASS_FACTORY or the retained ABI");
        pinned.put("FUNCTION_DECLARATION_EXPRESSION",
            "CLOSURE_NEW/RECURSIVE_GROUP_INIT and a LoweredFunction; adaptation explicit via FUNCTION_ADAPT (D15)");
        pinned.put("ASSIGNMENT", "ASSIGN address chain (D14): receiver \u2192 key \u2192 RHS \u2192 normalize "
            + "\u2192 write check (ARRAY_ELEMENT_ASSIGNMENT) \u2192 commit");
        pinned.put("DELETE", "DELETE address chain (D14): receiver \u2192 key \u2192 normalize \u2192 "
            + "[array bounds boundary (ARRAY_ELEMENT_DELETE)] \u2192 commit");
        pinned.put("HAS", "HAS_FIELD on a checked receiver/key, evaluated once each");
        pinned.put("AWAIT_ASYNC_CALL",
            "ASYNC_START (binding-resolved: DEAL_BODY/HOST/EXTERNAL), AWAIT per D13");
        pinned.put("VARIABLE_DECLARATION", "allocation, initializer, boundary, initialization");
        pinned.put("RETURN_EXPRESSION_STATEMENT", "RETURN (D13) or DISCARD");
        pinned.put("IF_WHILE_FOR_FOR_OF", "BRANCH, LOOP, or FOR_EACH");
        pinned.put("BREAK_CONTINUE", "matching loop-ID transfer");
        pinned.put("TRY_CATCH_THROW", "TRY_CATCH, THROW");
        pinned.put("CLASS_DECLARATION", "layout, defaults, factory, and export metadata");
        pinned.put("IMPORT_EXPORT_ENTRY",
            "module/import/export/entry operations plus interface/ABI records");
        pinned.put("STDLIB_TIME_NOW_MILLIS",
            "STDLIB_CALL(TIME_NOW_MILLIS) with the declared int "
                + "return boundary and its INT32_RESULT terminal");

        check(pinned.size() == 23, "exactly 23 rows carry a required common form; got " + pinned.size());
        int withForm = 0;
        for (ConstructKind kind : kinds) {
            String name = kind.name();
            check(pinned.containsKey(name),
                name + " carries the pinned required common form");
            withForm++;
            check(pinned.get(name).equals(kind.requiredCommonForm()),
                name + " required common form is the verbatim parent text (plus the K7 "
                    + "std.time row); got \""
                    + kind.requiredCommonForm() + "\"");
            check(!kind.mappedOpKinds().isEmpty(),
                name + " carries a non-empty mapped op-kind set");
        }
        check(withForm == 23, "23 rows carry a required common form; got " + withForm);

        // The K7 std.time row: its required common form and mapped kinds.
        check(ConstructKind.STDLIB_TIME_NOW_MILLIS.requiredCommonForm() != null
                && ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds()
                    .equals(List.of(SemanticOpKind.STDLIB_CALL, SemanticOpKind.BOUNDARY)),
            "the std.time.nowMillis row carries its required common form and the "
                + "[STDLIB_CALL, BOUNDARY] mapped kinds");

        // Pinned mapped op-kind sets for the exemplar rows.
        check(ConstructKind.CALL.mappedOpKinds().equals(List.of(
                SemanticOpKind.CALL, SemanticOpKind.CALLBACK_INVOKE, SemanticOpKind.INTRINSIC_CALL,
                SemanticOpKind.STDLIB_CALL, SemanticOpKind.ASYNC_START, SemanticOpKind.AWAIT)),
            "the call row maps to [CALL, CALLBACK_INVOKE, INTRINSIC_CALL, STDLIB_CALL, ASYNC_START, AWAIT]");
        check(ConstructKind.SCALAR_LITERAL.mappedOpKinds().equals(List.of(SemanticOpKind.CONST)),
            "the scalar literal row maps to [CONST]");
        check(ConstructKind.UNARY_ARITHMETIC_COMPARISON.mappedOpKinds().equals(List.of(
                SemanticOpKind.UNARY, SemanticOpKind.BINARY, SemanticOpKind.BRANCH)),
            "the unary/arithmetic/comparison row maps to [UNARY, BINARY, BRANCH]");
        check(ConstructKind.FUNCTION_DECLARATION_EXPRESSION.mappedOpKinds().equals(List.of(
                SemanticOpKind.CLOSURE_NEW, SemanticOpKind.RECURSIVE_GROUP_INIT,
                SemanticOpKind.FUNCTION_ADAPT)),
            "the function declaration/expression row maps to [CLOSURE_NEW, RECURSIVE_GROUP_INIT, FUNCTION_ADAPT]");
    }

    // =========================================================================
    // RuntimeDescriptor: canonical spec text goldens for every variant
    // =========================================================================

    static void testRuntimeDescriptorGoldens() {
        System.out.println("-- RuntimeDescriptor canonical spec text goldens --");

        check("null".equals(RuntimeDescriptor.Null.INSTANCE.canonicalSpecText()), "null -> \"null\"");
        check("boolean".equals(RuntimeDescriptor.Boolean.INSTANCE.canonicalSpecText()), "boolean -> \"boolean\"");
        check("int".equals(RuntimeDescriptor.Int.INSTANCE.canonicalSpecText()), "signed32 int -> \"int\"");
        check("number".equals(RuntimeDescriptor.Number.INSTANCE.canonicalSpecText()), "number -> \"number\"");
        check("string".equals(RuntimeDescriptor.String.INSTANCE.canonicalSpecText()), "string -> \"string\"");
        check("table".equals(RuntimeDescriptor.Table.INSTANCE.canonicalSpecText()), "table -> \"table\"");
        check("bytes".equals(RuntimeDescriptor.Bytes.INSTANCE.canonicalSpecText()),
            "bytes -> \"bytes\" (the ISSUE-0158 v1.2 bytes member)");
        check("[bytes]".equals(new RuntimeDescriptor.Array(RuntimeDescriptor.Bytes.INSTANCE).canonicalSpecText()),
            "array of bytes -> \"[bytes]\"");
        check("?bytes".equals(new RuntimeDescriptor.Nullable(RuntimeDescriptor.Bytes.INSTANCE).canonicalSpecText()),
            "nullable bytes -> \"?bytes\"");

        ClassId user = new ClassId("src/app", "User");
        check("@src/app/User".equals(new RuntimeDescriptor.Class(user).canonicalSpecText()),
            "class @src/app/User -> \"@src/app/User\"");

        check("[int]".equals(new RuntimeDescriptor.Array(RuntimeDescriptor.Int.INSTANCE).canonicalSpecText()),
            "array of int -> \"[int]\"");
        check("[[int]]".equals(new RuntimeDescriptor.Array(
                new RuntimeDescriptor.Array(RuntimeDescriptor.Int.INSTANCE)).canonicalSpecText()),
            "nested array -> \"[[int]]\"");
        check("[?@src/app/User]".equals(new RuntimeDescriptor.Array(
                new RuntimeDescriptor.Nullable(new RuntimeDescriptor.Class(user))).canonicalSpecText()),
            "array of nullable class -> \"[?@src/app/User]\"");

        check("?string".equals(new RuntimeDescriptor.Nullable(RuntimeDescriptor.String.INSTANCE).canonicalSpecText()),
            "nullable string -> \"?string\"");
        check("?@src/app/User".equals(new RuntimeDescriptor.Nullable(
                new RuntimeDescriptor.Class(user)).canonicalSpecText()),
            "nullable class -> \"?@src/app/User\" (NullableDescriptor := \"?\" RuntimeTypeDescriptor)");
        check("?[@src/app/User]".equals(new RuntimeDescriptor.Nullable(
                new RuntimeDescriptor.Array(new RuntimeDescriptor.Class(user))).canonicalSpecText()),
            "nullable array of class -> \"?[@src/app/User]\" (spec example: User[] | null)");

        RuntimeDescriptor.Func sync = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE, RuntimeDescriptor.String.INSTANCE),
            RuntimeDescriptor.Boolean.INSTANCE, false);
        check("(int,string)->boolean".equals(sync.canonicalSpecText()),
            "sync function -> \"(int,string)->boolean\"; got " + sync.canonicalSpecText());
        RuntimeDescriptor.Func nul = new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);
        check("()->null".equals(nul.canonicalSpecText()), "nullary function -> \"()->null\"");
        RuntimeDescriptor.Func async = new RuntimeDescriptor.Func(
            List.of(RuntimeDescriptor.Int.INSTANCE), RuntimeDescriptor.String.INSTANCE, true);
        check("async(int)->string".equals(async.canonicalSpecText()),
            "async function -> \"async(int)->string\"; got " + async.canonicalSpecText());

        // Pinned nullable invariants.
        expectRejected(() -> new RuntimeDescriptor.Nullable(RuntimeDescriptor.Null.INSTANCE),
            "Nullable(null) is rejected");
        expectRejected(() -> new RuntimeDescriptor.Nullable(
                new RuntimeDescriptor.Nullable(RuntimeDescriptor.String.INSTANCE)),
            "Nullable(Nullable(T)) is rejected");
        expectRejected(() -> new RuntimeDescriptor.Array(null), "Array(null) is rejected");
        expectRejected(() -> new RuntimeDescriptor.Class(null), "Class(null) is rejected");

        // Structural equality is authoritative.
        check(new RuntimeDescriptor.Class(user).equals(new RuntimeDescriptor.Class(new ClassId("src/app", "User"))),
            "descriptor equality is structural (record equality)");
        check(!new RuntimeDescriptor.Class(user).equals(new RuntimeDescriptor.Class(new ClassId("src/app", "Other"))),
            "different class ids are different descriptors");

        // No safe-range representation: int is a Java int (signed32).
        check(RuntimeDescriptor.Int.INSTANCE == RuntimeDescriptor.Int.INSTANCE,
            "the int descriptor is the signed32 singleton (no safe-range variant exists)");
    }

    // =========================================================================
    // Semantic ID types
    // =========================================================================

    static void testSemanticIds() {
        System.out.println("-- Semantic ID types --");

        ModuleId a = new ModuleId("a.b");
        check("a.b".equals(a.path()), "ModuleId carries the dotted module path");
        check(new ModuleId("a.b").equals(a), "ModuleId equality is the path");
        expectRejected(() -> new ModuleId(""), "empty ModuleId is rejected");
        expectRejected(() -> new ModuleId(null), "null ModuleId path is rejected");

        ClassId user = new ClassId("src/app", "User");
        check("@src/app/User".equals(user.text()), "ClassId text is @modulePath/ClassName");
        check("@/Error".equals(ClassId.ERROR.text()), "the builtin Error ClassId text is @/Error");
        expectRejected(() -> new ClassId("m", ""), "empty ClassId name is rejected");

        OpId op = new OpId(a, 7);
        check(a.equals(op.module()) && op.id() == 7, "OpId carries its module and numeric id");
        expectRejected(() -> new OpId(null, 1), "OpId rejects a null module");
        expectRejected(() -> new FunctionId(-1), "negative FunctionId is rejected");
        expectRejected(() -> new ValueId(-1), "negative ValueId is rejected");
        expectRejected(() -> new BindingId(-1), "negative BindingId is rejected");
        expectRejected(() -> new AnchorId(-1), "negative AnchorId is rejected");
        expectRejected(() -> new BlockId(-1), "negative BlockId is rejected");
        expectRejected(() -> new ClassFactoryId(-1), "negative ClassFactoryId is rejected");
        expectRejected(() -> new FunctionAllocationIdentity(-1),
            "negative FunctionAllocationIdentity is rejected");

        check(new OpId(a, 1) instanceof SemanticId, "OpId is a SemanticId");
        check(new ValueId(1) instanceof SemanticValue, "ValueId is a SemanticValue");
        check(new ValueId(1) instanceof SemanticId, "ValueId is a SemanticId");

        AsyncTokenId canonical = new AsyncTokenId.Canonical(3, AsyncTokenOwner.DEAL_BODY_TASK);
        check(canonical.tokenId() == 3 && canonical instanceof AsyncTokenId.Canonical
                && ((AsyncTokenId.Canonical) canonical).owner() == AsyncTokenOwner.DEAL_BODY_TASK,
            "CANONICAL token carries tokenId and owner");
        AsyncTokenId alias = new AsyncTokenId.Alias(4, canonical, AsyncLinkKind.ADAPTER_INNER);
        check(alias.tokenId() == 4 && ((AsyncTokenId.Alias) alias).referent() == canonical
                && ((AsyncTokenId.Alias) alias).linkKind() == AsyncLinkKind.ADAPTER_INNER,
            "ALIAS token carries tokenId, referent, and linkKind");
        expectRejected(() -> new AsyncTokenId.Canonical(-1, AsyncTokenOwner.HOST_OPERATION),
            "negative tokenId is rejected");
        expectRejected(() -> new AsyncTokenId.Alias(1, null, AsyncLinkKind.EXTERNAL_LINK),
            "ALIAS rejects a null referent");
    }

    // =========================================================================
    // FunctionExecutionBinding / BoundaryRealization / AdaptSourceRef shapes
    // =========================================================================

    static void testBindingShapes() {
        System.out.println("-- FunctionExecutionBinding and BoundaryRealization shapes --");

        FunctionId fn = new FunctionId(0);
        BlockId block = new BlockId(0);
        FunctionExecutionBinding body = new FunctionExecutionBinding.LoweredBody(fn, block);
        check(body instanceof FunctionExecutionBinding.LoweredBody
                && ((FunctionExecutionBinding.LoweredBody) body).functionId() == fn
                && ((FunctionExecutionBinding.LoweredBody) body).blockId() == block,
            "LoweredBody carries functionId and blockId");

        RuntimeDescriptor.Func sig = new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);
        FunctionExecutionBinding host = new FunctionExecutionBinding.HostFunction(
            new ModuleId("host.a"), "export", sig);
        check(host instanceof FunctionExecutionBinding.HostFunction,
            "HostFunction carries hostModuleId/exportName/descriptor");
        FunctionExecutionBinding hostValue = new FunctionExecutionBinding.HostFunctionValue(
            new ModuleId("host.a"), new OpId(new ModuleId("m"), 1), sig);
        check(hostValue instanceof FunctionExecutionBinding.HostFunctionValue
                && ((FunctionExecutionBinding.HostFunctionValue) hostValue).materializingBoundaryOpId() != null,
            "HostFunctionValue names its materializing boundary op");
        FunctionExecutionBinding ext = new FunctionExecutionBinding.ExternalFunction(
            new ModuleId("b"), "export", sig, ExternalExecutionOwner.SHARED_BODY);
        check(ext instanceof FunctionExecutionBinding.ExternalFunction
                && ((FunctionExecutionBinding.ExternalFunction) ext).executionOwner()
                    == ExternalExecutionOwner.SHARED_BODY,
            "ExternalFunction carries executionOwner SHARED_BODY");
        FunctionExecutionBinding adapter = new FunctionExecutionBinding.AdapterBinding(
            new OpId(new ModuleId("m"), 2), CaptureMode.SHARED_CELL,
            new AdaptSourceRef.SharedCell(new BindingId(1), 0), sig, sig);
        check(adapter instanceof FunctionExecutionBinding.AdapterBinding
                && ((FunctionExecutionBinding.AdapterBinding) adapter).sourceRef()
                    instanceof AdaptSourceRef.SharedCell,
            "AdapterBinding carries adaptOpId/captureMode/sourceRef/signatures");

        FunctionExecutionBinding intrinsic = new FunctionExecutionBinding.IntrinsicFunction(
            IntrinsicKind.INT_CONVERT, IntrinsicKind.INT_CONVERT.declaredSignature());
        check(intrinsic instanceof FunctionExecutionBinding.IntrinsicFunction value
                && value.kind() == IntrinsicKind.INT_CONVERT
                && value.descriptor()
                    .equals(IntrinsicKind.INT_CONVERT.declaredSignature()),
            "IntrinsicFunction carries kind and descriptor (ISSUE-0632)");

        OpId materializing = new OpId(new ModuleId("m"), 7);
        FunctionExecutionBinding dynamic =
            new FunctionExecutionBinding.DynamicFunctionValue(materializing, sig);
        check(dynamic instanceof FunctionExecutionBinding.DynamicFunctionValue value
                && value.materializingOpId().equals(materializing)
                && value.descriptor().equals(sig),
            "DynamicFunctionValue carries the producing op id and the descriptor "
                + "(ISSUE-0673)");

        Set<Class<?>> permitted = Set.copyOf(Arrays.asList(
            FunctionExecutionBinding.LoweredBody.class,
            FunctionExecutionBinding.AdapterBinding.class,
            FunctionExecutionBinding.HostFunction.class,
            FunctionExecutionBinding.HostFunctionValue.class,
            FunctionExecutionBinding.ExternalFunction.class,
            FunctionExecutionBinding.IntrinsicFunction.class,
            FunctionExecutionBinding.DynamicFunctionValue.class));
        check(FunctionExecutionBinding.class.isSealed()
                && permitted.equals(Set.copyOf(Arrays.asList(FunctionExecutionBinding.class.getPermittedSubclasses()))),
            "FunctionExecutionBinding is sealed over exactly the 7 pinned variants");

        BoundaryRealization checkOp = new BoundaryRealization.RuntimeValidation("check-1");
        BoundaryRealization proof = new BoundaryRealization.RepresentationProof("jvm-int-proof");
        check(checkOp instanceof BoundaryRealization.RuntimeValidation
                && "check-1".equals(((BoundaryRealization.RuntimeValidation) checkOp).checkId()),
            "RuntimeValidation carries the check id");
        check(proof instanceof BoundaryRealization.RepresentationProof
                && "jvm-int-proof".equals(((BoundaryRealization.RepresentationProof) proof).proofKind()),
            "RepresentationProof carries the proof kind");
        check(BoundaryRealization.class.isSealed()
                && Set.copyOf(Arrays.asList(BoundaryRealization.class.getPermittedSubclasses())).equals(Set.of(
                    BoundaryRealization.RuntimeValidation.class,
                    BoundaryRealization.RepresentationProof.class)),
            "BoundaryRealization is sealed over exactly RuntimeValidation + RepresentationProof");
        expectRejected(() -> new BoundaryRealization.RuntimeValidation(null),
            "RuntimeValidation rejects a null check id");

        BindingGeneration gen = new BindingGeneration(new BindingId(1), 2);
        check(gen.generation() == 2 && gen.binding() instanceof BindingId,
            "BindingGeneration pairs binding and generation");
        BindingImmutabilityProof immut = new BindingImmutabilityProof(new BindingId(1), 2);
        check(immut.binding() instanceof BindingId && immut.generation() == 2,
            "BindingImmutabilityProof pairs binding and generation");
        AdaptSourceRef thunk = new AdaptSourceRef.Thunk(new BlockId(1), List.of(gen));
        check(thunk instanceof AdaptSourceRef.Thunk
                && ((AdaptSourceRef.Thunk) thunk).capturedBindings().equals(List.of(gen)),
            "Thunk source records the lowered thunk block and generation-pinned captures");
        AdaptSourceRef value = new AdaptSourceRef.Value(new ValueId(9));
        check(value instanceof AdaptSourceRef.Value, "Value source retains the materialized value id");

        ExternalAsyncLink link = new ExternalAsyncLink(new ModuleId("b"), "asyncExport", canonicalToken());
        check(link.calleeModuleId().equals(new ModuleId("b")) && "asyncExport".equals(link.exportName())
                && link.calleeTokenId() instanceof AsyncTokenId,
            "ExternalAsyncLink carries {calleeModuleId, exportName, calleeTokenId}");
    }

    private static AsyncTokenId canonicalToken() {
        return new AsyncTokenId.Canonical(5, AsyncTokenOwner.DEAL_BODY_TASK);
    }

    // =========================================================================
    // Payload construction: one shape per kind; mandatory fields enforced
    // =========================================================================

    private static final ModuleId MOD = new ModuleId("m");
    private static final ClassId CLS = new ClassId("m", "C");
    private static final RuntimeDescriptor.Func SIG =
        new RuntimeDescriptor.Func(List.of(), RuntimeDescriptor.Null.INSTANCE);
    private static final ClassLayout LAYOUT = new ClassLayout(CLS, List.of(
        new ClassLayout.FieldLayout("f", RuntimeDescriptor.Int.INSTANCE, false, DefaultOwner.LOCAL)));

    static KindPayload minimalPayload(SemanticOpKind kind) {
        ValueId v0 = new ValueId(0);
        ValueId v1 = new ValueId(1);
        BlockId b0 = new BlockId(0);
        OpId o0 = new OpId(MOD, 0);
        OpId o1 = new OpId(MOD, 1);
        return switch (kind) {
            case CONST -> new KindPayload.ConstPayload(new ScalarValue.Int(1));
            case UNARY -> new KindPayload.UnaryPayload(UnarySelector.BOOL_NOT);
            case BINARY -> new KindPayload.BinaryPayload(BinarySelector.INT32_ADD, null, null);
            case STRING_CONCAT -> new KindPayload.StringConcatPayload(List.of(v0, v1));
            case ARRAY_NEW -> new KindPayload.ArrayNewPayload(RuntimeDescriptor.Int.INSTANCE,
                List.of(v0), List.of(o0));
            case TABLE_NEW -> new KindPayload.TableNewPayload(
                List.of(new KindPayload.TableEntry("k", v0)));
            case ARRAY_LENGTH -> new KindPayload.ArrayLengthPayload(v0);
            case MEMBER_READ -> new KindPayload.MemberReadPayload(v0, "k");
            case MEMBER_WRITE -> new KindPayload.MemberWritePayload(v0, "k", v1);
            case MEMBER_DELETE -> new KindPayload.MemberDeletePayload(v0, "k");
            case INDEX_NORMALIZE -> new KindPayload.IndexNormalizePayload(
                IndexMode.ARRAY_READ, v0, v1);
            case INDEX_READ -> new KindPayload.IndexReadPayload(v0, v1, o0);
            case INDEX_WRITE -> new KindPayload.IndexWritePayload(v0, v1, new ValueId(2));
            case INDEX_DELETE -> new KindPayload.IndexDeletePayload(v0, v1);
            case OPTIONAL_READ -> new KindPayload.OptionalReadPayload(v0, true, RuntimeDescriptor.Int.INSTANCE);
            case HAS_FIELD -> new KindPayload.HasFieldPayload(v0, "k");
            case BOUNDARY -> new KindPayload.BoundaryPayload(BoundaryKind.MODULE_EXPORT,
                RuntimeDescriptor.Int.INSTANCE, v0, new BoundaryRealization.RuntimeValidation("c"));
            case BINDING_ALLOC -> new KindPayload.BindingAllocPayload(
                new BindingId(0), b0, false, BindingCellKind.DIRECT, 0);
            case BINDING_INIT -> new KindPayload.BindingInitPayload(new BindingId(0), 0, v0);
            case BINDING_LOAD -> new KindPayload.BindingLoadPayload(new BindingId(0), 0);
            case BINDING_STORE -> new KindPayload.BindingStorePayload(new BindingId(0), 0, v0);
            case RECURSIVE_GROUP_INIT -> new KindPayload.RecursiveGroupInitPayload(
                List.of(new BindingId(0)), List.of(new FunctionId(0)));
            case CLOSURE_NEW -> new KindPayload.ClosureNewPayload(new FunctionId(0), SIG,
                List.of(), new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0));
            case FUNCTION_ADAPT -> new KindPayload.FunctionAdaptPayload(SIG, SIG,
                CaptureMode.SHARED_CELL, new AdaptSourceRef.SharedCell(new BindingId(0), 0), null);
            case ASSIGN -> new KindPayload.AssignPayload(AssignTargetKind.VARIABLE,
                List.of(o0, o1));
            case DELETE -> new KindPayload.DeletePayload(DeleteTargetKind.TABLE_SLOT,
                List.of(o0, o1));
            case CALL -> new KindPayload.CallPayload(CallMode.DIRECT,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0)),
                SIG, List.of(), null, null, b0, null);
            case EXTERNAL_ENTRY -> new KindPayload.ExternalEntryPayload(
                "export", new FunctionId(0), SIG, false, o0, null);
            case CALLBACK_INVOKE -> new KindPayload.CallbackInvokePayload(
                v0, SIG, List.of(), o0);
            case INTRINSIC_CALL -> new KindPayload.IntrinsicCallPayload(
                IntrinsicKind.INT_CONVERT, v0);
            case STDLIB_CALL -> new KindPayload.StdlibCallPayload(
                StdlibFunctionId.MATH_FLOOR, List.of(v0), SemanticCapability.STDLIB_SEMANTICS);
            case ASYNC_START -> new KindPayload.AsyncStartPayload(
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(0), b0)),
                AsyncStartSource.DEAL_BODY, ParameterBoundaryMode.RUN, List.of(),
                RuntimeDescriptor.Null.INSTANCE, o0, null, null);
            case AWAIT -> new KindPayload.AwaitPayload(canonicalToken(),
                RuntimeDescriptor.Null.INSTANCE, o0);
            case BRANCH -> new KindPayload.BranchPayload(ControlSelector.IF, v0, b0, null);
            case LOOP -> new KindPayload.LoopPayload(ControlSelector.WHILE, null, v0, b0, null);
            case FOR_EACH -> new KindPayload.ForEachPayload(IterationMode.ARRAY_VALUES,
                v0, new BindingId(0), 0, b0);
            case TRY_CATCH -> new KindPayload.TryCatchPayload(b0, new BindingId(0), new BlockId(1));
            case THROW -> new KindPayload.ThrowPayload(v0);
            case RETURN -> new KindPayload.ReturnPayload(null, new FunctionId(0), o0, o1);
            case BREAK -> new KindPayload.BreakPayload(o0);
            case CONTINUE -> new KindPayload.ContinuePayload(o0);
            case DISCARD -> new KindPayload.DiscardPayload(v0);
            case CLASS_DEFAULT -> new KindPayload.ClassDefaultPayload(CLS, "f", b0);
            case CLASS_NEW -> new KindPayload.ClassNewPayload(CLS, LAYOUT,
                List.of(), DefaultOwner.LOCAL, List.of(), null, List.of());
            case CLASS_FACTORY -> new KindPayload.ClassFactoryPayload(CLS, List.of(), o0);
            case FIELD_READ -> new KindPayload.FieldReadPayload(v0, CLS, "f");
            case FIELD_WRITE -> new KindPayload.FieldWritePayload(v0, CLS, "f", v1);
            case FIELD_DELETE -> new KindPayload.FieldDeletePayload(v0, CLS, "f");
            case JSON_FROM_CLASS -> new KindPayload.JsonFromClassPayload(LAYOUT, v0);
            case JSON_TO_CLASS -> new KindPayload.JsonToClassPayload(v0, LAYOUT);
            case MODULE_INIT -> new KindPayload.ModuleInitPayload(MOD, List.of(), b0);
            case MODULE_IMPORT -> new KindPayload.ModuleImportPayload(
                "a", new ModuleId("a"), ModuleImportKind.COMPILED);
            case EXPORT_READ -> new KindPayload.ExportReadPayload(
                new ModuleId("a"), "x", RuntimeDescriptor.Int.INSTANCE, v0);
            case EXPORT_PUBLISH -> new KindPayload.ExportPublishPayload(
                MOD, "x", RuntimeDescriptor.Int.INSTANCE, v0);
            case ENTRY_INVOKE -> new KindPayload.EntryInvokePayload(MOD, new FunctionId(0));
        };
    }

    static void testPayloadConstruction() {
        System.out.println("-- Payload construction: one constructor per kind --");

        check(SemanticOpKind.values().length == 55, "SemanticOpKind has exactly 55 values");

        Set<Class<?>> seen = new java.util.HashSet<>();
        for (SemanticOpKind kind : SemanticOpKind.values()) {
            Class<? extends KindPayload> payloadClass = kind.payloadClass();
            check(payloadClass != null, kind + " maps to a payload class");
            check(payloadClass.isRecord(),
                kind + " payload " + payloadClass.getSimpleName() + " is an immutable record");
            check(Modifier.isFinal(payloadClass.getModifiers()) || payloadClass.isRecord(),
                kind + " payload cannot be extended");
            check(seen.add(payloadClass),
                kind + " has a distinct payload shape (no duplicate mapping)");
            KindPayload payload = minimalPayload(kind);
            check(payloadClass.isInstance(payload),
                kind + " minimal payload is an instance of " + payloadClass.getSimpleName());
        }
        check(seen.size() == 55, "55 distinct payload shapes for the 55 kinds; got " + seen.size());

        // Pinned mandatory-field rejections.
        expectRejected(() -> new KindPayload.CallPayload(null,
                new KindPayload.CallCallee.Static(
                    new FunctionExecutionBinding.LoweredBody(new FunctionId(0), new BlockId(0))),
                SIG, List.of(), null, null, null, null),
            "CALL without CallMode cannot be constructed (null mode rejected)");
        check(KindPayload.CallPayload.class.getRecordComponents().length == 8
                && KindPayload.CallPayload.class.getRecordComponents()[0].getType() == CallMode.class
                && KindPayload.CallPayload.class.getRecordComponents()[5].getType()
                    == KindPayload.DynamicReturnBoundary.class,
            "CALL payload's first mandatory component is the CallMode and its sixth is the "
                + "closed DynamicReturnBoundary set (no constructor without either)");

        expectRejected(() -> new KindPayload.BoundaryPayload(BoundaryKind.MODULE_EXPORT,
                RuntimeDescriptor.Int.INSTANCE, new ValueId(0), null),
            "BOUNDARY without realization cannot be constructed (null realization rejected)");
        check(KindPayload.BoundaryPayload.class.getRecordComponents().length == 4
                && KindPayload.BoundaryPayload.class.getRecordComponents()[3].getType()
                    == BoundaryRealization.class,
            "BOUNDARY payload's realization component is the closed BoundaryRealization type");

        expectRejected(() -> new KindPayload.ClassNewPayload(CLS, LAYOUT, List.of(), null,
                List.of(), null, List.of()),
            "CLASS_NEW without defaultOwner cannot be constructed (null defaultOwner rejected)");
        check(KindPayload.ClassNewPayload.class.getRecordComponents()[3].getType() == DefaultOwner.class,
            "CLASS_NEW payload's defaultOwner component is the closed DefaultOwner type");

        // Selector wiring for the selector-carrying payloads.
        check(new KindPayload.UnaryPayload(UnarySelector.INT32_NEG).selector() == UnarySelector.INT32_NEG,
            "UnaryPayload carries its exact selector");
        check(new KindPayload.BinaryPayload(BinarySelector.NUMBER_ADD, null, null).selector()
                == BinarySelector.NUMBER_ADD,
            "BinaryPayload carries its exact selector");
        check(new KindPayload.StdlibCallPayload(StdlibFunctionId.JSON_PARSE, List.of(),
                SemanticCapability.STDLIB_SEMANTICS).selector() == StdlibFunctionId.JSON_PARSE,
            "StdlibCallPayload carries its exact selector (StdlibFunctionId is a ClosedSelector)");
        check(UnarySelector.BOOL_NOT instanceof ClosedSelector
                && BinarySelector.INT32_EQ instanceof ClosedSelector
                && StdlibFunctionId.CONSOLE_LOG instanceof ClosedSelector,
            "UnarySelector/BinarySelector/StdlibFunctionId are the closed selector family");
    }

    // =========================================================================
    // SemanticOp and OperationContractSnapshot wiring
    // =========================================================================

    static SourceOrigin origin() {
        return new SourceOrigin("m.deal", SourceSpan.synthetic("m.deal"),
            SourceOriginKind.SYNTHETIC, new AnchorId(0), null);
    }

    static OperationContractSnapshot snapshotFor(KindPayload payload, SemanticOpKind kind,
                                                OpResultType resultType,
                                                List<RuntimeDescriptor> operandTypes,
                                                FailurePolicyId policy, String digest) {
        ClosedSelector selector = payload instanceof KindPayload.SelectorCarrying carrying
            ? carrying.selector()
            : null;
        return new OperationContractSnapshot(1, kind, resultType, operandTypes, selector,
            payload, policy, List.of(), digest);
    }

    static SemanticOp op(SemanticOpKind kind, KindPayload payload, SemanticValue result,
                         OpResultType resultType, List<ValueId> operands,
                         List<RuntimeDescriptor> operandTypes, FailurePolicyId policy) {
        OperationContractSnapshot snap = snapshotFor(payload, kind, resultType, operandTypes,
            policy, "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
        return new SemanticOp(new OpId(MOD, 1), kind, origin(), result, resultType,
            operands, operandTypes, payload, policy, snap);
    }

    static void testSemanticOpWiring() {
        System.out.println("-- SemanticOp / OperationContractSnapshot wiring --");

        check(OperationContractSnapshot.class.isRecord(), "OperationContractSnapshot is a record");
        RecordComponent[] snapComponents = OperationContractSnapshot.class.getRecordComponents();
        check(snapComponents.length == 9,
            "OperationContractSnapshot has exactly 9 components; got " + snapComponents.length);
        check(snapComponents[0].getName().equals("version")
                && snapComponents[0].getType() == int.class,
            "snapshot component 0 is version: int");
        check(snapComponents[8].getName().equals("canonicalDigest"),
            "snapshot component 8 is canonicalDigest");
        check(OperationContractSnapshot.VERSION == 1, "snapshot version is pinned to 1");

        expectRejected(() -> new OperationContractSnapshot(2, SemanticOpKind.CONST,
                RuntimeDescriptor.Int.INSTANCE, List.of(), null,
                new KindPayload.ConstPayload(new ScalarValue.Int(1)), FailurePolicyId.NO_DEAL_FAILURE,
                List.of(), "d"),
            "a snapshot version other than 1 is rejected");

        KindPayload payload = new KindPayload.ConstPayload(new ScalarValue.Int(1));
        SemanticOp constOp = op(SemanticOpKind.CONST, payload, new ValueId(5),
            RuntimeDescriptor.Int.INSTANCE, List.of(), List.of(), FailurePolicyId.NO_DEAL_FAILURE);
        check(constOp.contract().opKind() == SemanticOpKind.CONST
                && constOp.contract().payload() == payload
                && constOp.contract().resultType() == RuntimeDescriptor.Int.INSTANCE
                && constOp.contract().operandTypes().isEmpty()
                && constOp.contract().failurePolicy() == FailurePolicyId.NO_DEAL_FAILURE
                && constOp.contract().selector() == null,
            "the op's contract is wired from the op's own fields (no selector for CONST)");

        // Selector extraction via the wiring helper.
        KindPayload unary = new KindPayload.UnaryPayload(UnarySelector.NUMBER_NEG);
        SemanticOp unaryOp = op(SemanticOpKind.UNARY, unary, new ValueId(6),
            RuntimeDescriptor.Boolean.INSTANCE, List.of(new ValueId(7)),
            List.of(RuntimeDescriptor.Boolean.INSTANCE), FailurePolicyId.NO_DEAL_FAILURE);
        check(unaryOp.contract().selector() == UnarySelector.NUMBER_NEG,
            "the wiring extracts the exact closed selector from a selector-carrying payload");
        check(OperationContractSnapshot.of(unaryOp, List.of(), unaryOp.contract().canonicalDigest())
                .equals(unaryOp.contract()),
            "OperationContractSnapshot.of mirrors the op's own wired snapshot");

        // Digest is carried opaque (computed by T3, checked by T6).
        check("d".equals(OperationContractSnapshot.of(unaryOp, List.of(), "d").canonicalDigest()),
            "the canonicalDigest field is carried verbatim");

        // Closed typed surface: kind/payload mismatch is rejected.
        expectRejected(() -> op(SemanticOpKind.UNARY, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                new ValueId(1), RuntimeDescriptor.Int.INSTANCE, List.of(), List.of(),
                FailurePolicyId.NO_DEAL_FAILURE),
            "a UNARY op with a CONST payload cannot be constructed");
        expectRejected(() -> new SemanticOp(new OpId(MOD, 1), SemanticOpKind.CONST, origin(),
                new ValueId(1), RuntimeDescriptor.Int.INSTANCE, List.of(), List.of(),
                new KindPayload.ConstPayload(new ScalarValue.Int(1)), FailurePolicyId.NO_DEAL_FAILURE,
                snapshotFor(new KindPayload.ConstPayload(new ScalarValue.Int(2)), SemanticOpKind.CONST,
                    RuntimeDescriptor.Int.INSTANCE, List.of(), FailurePolicyId.NO_DEAL_FAILURE, "d")),
            "a contract whose payload differs from the op's payload is rejected");
        expectRejected(() -> op(SemanticOpKind.CONST, new KindPayload.ConstPayload(new ScalarValue.Int(1)),
                new ValueId(1), RuntimeDescriptor.Int.INSTANCE, List.of(new ValueId(1)),
                List.of(), FailurePolicyId.NO_DEAL_FAILURE),
            "operands/operandTypes length mismatch is rejected");

        // SourceOrigin pinned shape.
        check(SourceOrigin.class.isRecord() && SourceOrigin.class.getRecordComponents().length == 5,
            "SourceOrigin has the pinned 5 components {sourceId, span, kind, anchorId, parentOpId?}");
        SourceOrigin user = new SourceOrigin("m.deal", new SourceSpan("m.deal", 1, 1, 1, 4),
            SourceOriginKind.USER, new AnchorId(1), new OpId(MOD, 0));
        check(user.kind() == SourceOriginKind.USER && user.parentOpId() != null,
            "SourceOrigin carries USER|SYNTHETIC and an optional parentOpId");
        SourceSpan span = new SourceSpan("f.deal", 2, 3, 2, 9, 10, 20);
        check(span.hasScalarOffsets() && span.startLine() == 2 && span.startColumn() == 3
                && span.endColumn() == 9 && span.startScalarOffset() == 10 && span.endScalarOffset() == 20,
            "SourceSpan mirrors the checked 1-based inclusive span contract with scalar offsets");
        check(!SourceSpan.synthetic("f.deal").hasScalarOffsets(),
            "synthetic spans carry UNKNOWN_OFFSET scalar offsets");
        expectRejected(() -> new SourceSpan("f", 2, 1, 1, 1),
            "an inverted span is rejected");
    }

    // =========================================================================
    // CapabilityRequirementCatalog + T1 SemanticCapability integration
    // =========================================================================

    static void testCapabilityCatalog() {
        System.out.println("-- CapabilityRequirementCatalog (T1 integration) --");

        Map<SemanticCapability, List<CapabilityRequirementCatalog.RequiredOperation>> catalog =
            CapabilityRequirementCatalog.catalog();
        check(catalog.keySet().equals(EnumSet.allOf(SemanticCapability.class)),
            "the catalog covers every closed SemanticCapability (keyed by T1's enum)");
        check(catalog.size() == 12, "the catalog has exactly 12 capability rows; got " + catalog.size());

        check(verbatim(catalog, SemanticCapability.FOUNDATION_VALUES).equals(List.of(
                "CONST", "UNARY", "BINARY", "STRING_CONCAT")),
            "FOUNDATION_VALUES → {CONST, UNARY, BINARY, STRING_CONCAT}");
        check(verbatim(catalog, SemanticCapability.SIGNED_INT32).equals(List.of(
                "CONST(Int)", "UNARY(INT32_*)", "BINARY(INT32_*)", "INTRINSIC_CALL(INT_CONVERT)",
                "BOUNDARY(int descriptor)")),
            "SIGNED_INT32 → {CONST(Int), UNARY(INT32_*), BINARY(INT32_*), INTRINSIC_CALL(INT_CONVERT), BOUNDARY(int descriptor)}");
        check(verbatim(catalog, SemanticCapability.CONTAINERS_AND_STRINGS).equals(List.of(
                "ARRAY_NEW", "TABLE_NEW", "ARRAY_LENGTH", "MEMBER_*", "INDEX_*", "OPTIONAL_READ",
                "HAS_FIELD", "FOR_EACH")),
            "CONTAINERS_AND_STRINGS → {ARRAY_NEW, TABLE_NEW, ARRAY_LENGTH, MEMBER_*, INDEX_*, OPTIONAL_READ, HAS_FIELD, FOR_EACH}");
        check(verbatim(catalog, SemanticCapability.DESCRIPTORS).equals(List.of("BOUNDARY")),
            "DESCRIPTORS → {BOUNDARY}");
        check(verbatim(catalog, SemanticCapability.BOUNDARIES).equals(List.of("BOUNDARY")),
            "BOUNDARIES → {BOUNDARY}");
        check(verbatim(catalog, SemanticCapability.EVALUATION_ORDER).equals(List.of(
                "BRANCH", "LOOP", "DISCARD")),
            "EVALUATION_ORDER → {BRANCH, LOOP, DISCARD}");
        check(verbatim(catalog, SemanticCapability.BINDINGS).equals(List.of(
                "BINDING_ALLOC", "BINDING_INIT", "BINDING_LOAD", "BINDING_STORE",
                "RECURSIVE_GROUP_INIT", "CLOSURE_NEW")),
            "BINDINGS → {BINDING_ALLOC, BINDING_INIT, BINDING_LOAD, BINDING_STORE, RECURSIVE_GROUP_INIT, CLOSURE_NEW}");
        check(verbatim(catalog, SemanticCapability.CALLS).equals(List.of(
                "CALL", "CALLBACK_INVOKE", "EXTERNAL_ENTRY", "ASYNC_START", "AWAIT", "RETURN",
                "ENTRY_INVOKE", "FUNCTION_ADAPT")),
            "CALLS → {CALL, CALLBACK_INVOKE, EXTERNAL_ENTRY, ASYNC_START, AWAIT, RETURN, ENTRY_INVOKE, FUNCTION_ADAPT}");
        check(verbatim(catalog, SemanticCapability.STDLIB_SEMANTICS).equals(List.of("STDLIB_CALL")),
            "STDLIB_SEMANTICS → {STDLIB_CALL}");
        check(catalog.get(SemanticCapability.STDLIB_TIME_CONFLICT).isEmpty(),
            "STDLIB_TIME_CONFLICT → {} (routing marker, never valid IR)");
        check(verbatim(catalog, SemanticCapability.CLASSES).equals(List.of(
                "CLASS_NEW", "CLASS_FACTORY", "CLASS_DEFAULT", "FIELD_READ", "FIELD_WRITE",
                "FIELD_DELETE", "JSON_FROM_CLASS", "JSON_TO_CLASS")),
            "CLASSES → {CLASS_NEW, CLASS_FACTORY, CLASS_DEFAULT, FIELD_READ, FIELD_WRITE, FIELD_DELETE, JSON_FROM_CLASS, JSON_TO_CLASS}");
        check(verbatim(catalog, SemanticCapability.MODULES).equals(List.of(
                "MODULE_INIT", "MODULE_IMPORT", "EXPORT_READ", "EXPORT_PUBLISH")),
            "MODULES → {MODULE_INIT, MODULE_IMPORT, EXPORT_READ, EXPORT_PUBLISH}");

        // Wildcards expanded to concrete kinds.
        CapabilityRequirementCatalog.RequiredOperation members =
            catalog.get(SemanticCapability.CONTAINERS_AND_STRINGS).get(3);
        check(members.kinds().equals(List.of(SemanticOpKind.MEMBER_READ, SemanticOpKind.MEMBER_WRITE,
                SemanticOpKind.MEMBER_DELETE)),
            "MEMBER_* expands to the three member kinds");
        CapabilityRequirementCatalog.RequiredOperation indexes =
            catalog.get(SemanticCapability.CONTAINERS_AND_STRINGS).get(4);
        check(indexes.kinds().equals(List.of(SemanticOpKind.INDEX_NORMALIZE,
                SemanticOpKind.INDEX_READ, SemanticOpKind.INDEX_WRITE, SemanticOpKind.INDEX_DELETE)),
            "INDEX_* expands to the four index kinds");

        // Synthetic unit integration: keys are T1's enum values; an
        // out-of-set capability cannot be expressed.
        LoweredModuleUnit unit = syntheticUnit(
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES, SemanticCapability.SIGNED_INT32));
        check(unit.requiredCapabilities().equals(EnumSet.of(
                SemanticCapability.FOUNDATION_VALUES, SemanticCapability.SIGNED_INT32)),
            "the synthetic unit's requiredCapabilities are keyed by T1's SemanticCapability values");
        expectRejected(() -> SemanticCapability.valueOf("OUT_OF_SET"),
            "an out-of-set capability cannot be expressed (closed enum)");
    }

    private static List<String> verbatim(
            Map<SemanticCapability, List<CapabilityRequirementCatalog.RequiredOperation>> catalog,
            SemanticCapability capability) {
        List<String> result = new ArrayList<>();
        for (CapabilityRequirementCatalog.RequiredOperation op : catalog.get(capability)) {
            result.add(op.verbatim());
        }
        return result;
    }

    // =========================================================================
    // LoweredModuleUnit / ExecutableLoweredProject pinned constraints
    // =========================================================================

    static LoweredModuleUnit syntheticUnit(Set<SemanticCapability> capabilities) {
        return new LoweredModuleUnit(
            LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32,
            new ModuleId("entry"),
            "interface-hash",
            "lowering-context-hash",
            capabilities,
            Map.of(),
            Map.of(),
            Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)),
            ExportPlan.empty(),
            Map.of());
    }

    static void testUnitAndProject() {
        System.out.println("-- LoweredModuleUnit / ExecutableLoweredProject pinned constraints --");

        check("deal.semantic-ir/1".equals(LoweredModuleUnit.FORMAT_VERSION),
            "the unit format version is pinned to deal.semantic-ir/1");
        check("deal.semantic-interface/1".equals(ProjectInterfaceIndex.FORMAT_VERSION),
            "the index format version is pinned to deal.semantic-interface/1");

        // No constructor path admits a profile other than DEAL_V1_2_INT32.
        expectRejected(() -> new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
                SemanticProfile.LEGACY_SAFE_INT, new ModuleId("m"), "ih", "lch",
                EnumSet.noneOf(SemanticCapability.class), Map.of(), Map.of(), Map.of(),
                new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of()),
            "a LEGACY_SAFE_INT unit cannot be constructed");
        expectRejected(() -> new LoweredModuleUnit("deal.semantic-ir/2",
                SemanticProfile.DEAL_V1_2_INT32, new ModuleId("m"), "ih", "lch",
                EnumSet.noneOf(SemanticCapability.class), Map.of(), Map.of(), Map.of(),
                new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of()),
            "a unit with a foreign format version is rejected");

        LoweredModuleUnit unit = syntheticUnit(
            EnumSet.of(SemanticCapability.FOUNDATION_VALUES, SemanticCapability.SIGNED_INT32));
        check(unit.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32,
            "the constructed unit carries DEAL_V1_2_INT32");

        // The K7 std.time.nowMillis row is an ordinary constructCoverage
        // key carrying the closed mapped op kinds verbatim.
        EnumMap<ConstructKind, List<SemanticOpKind>> coverage = new EnumMap<>(ConstructKind.class);
        coverage.put(ConstructKind.CALL, ConstructKind.CALL.mappedOpKinds());
        LoweredModuleUnit covered = new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, new ModuleId("m"), "ih", "lch",
            EnumSet.of(SemanticCapability.CALLS), coverage, Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of());
        check(covered.constructCoverage().get(ConstructKind.CALL)
                .equals(ConstructKind.CALL.mappedOpKinds()),
            "constructCoverage is enum-keyed and carries the mapped op-kind list");
        EnumMap<ConstructKind, List<SemanticOpKind>> withTime = new EnumMap<>(ConstructKind.class);
        withTime.put(ConstructKind.STDLIB_TIME_NOW_MILLIS,
            ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds());
        LoweredModuleUnit timeCovered = new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, new ModuleId("m"), "ih", "lch",
            EnumSet.of(SemanticCapability.STDLIB_SEMANTICS), withTime, Map.of(), Map.of(),
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of());
        check(timeCovered.constructCoverage()
                .get(ConstructKind.STDLIB_TIME_NOW_MILLIS)
                .equals(ConstructKind.STDLIB_TIME_NOW_MILLIS.mappedOpKinds()),
            "the std/time.nowMillis row is an ordinary constructCoverage key carrying the "
                + "mapped op-kind list (K7)");

        // Immutability: the unit defensively copies its maps.
        Map<FunctionId, LoweredFunction> functions = new LinkedHashMap<>();
        FunctionId fn = new FunctionId(1);
        functions.put(fn, new LoweredFunction(fn, SIG, List.of(), new BlockId(1)));
        LoweredModuleUnit withFunctions = new LoweredModuleUnit(LoweredModuleUnit.FORMAT_VERSION,
            SemanticProfile.DEAL_V1_2_INT32, new ModuleId("m"), "ih", "lch",
            EnumSet.of(SemanticCapability.BINDINGS), Map.of(), Map.of(), functions,
            new ModuleInitPlan(List.of(), new BlockId(0)), ExportPlan.empty(), Map.of());
        functions.clear();
        check(withFunctions.functions().containsKey(fn),
            "the unit's maps are defensive copies (no identity-keyed or aliased frontend state)");
        expectRejected(() -> withFunctions.functions().clear(),
            "the unit's maps are unmodifiable");

        // Lowering context formula pinned in the schema.
        LoweringContext context = new LoweringContext(SemanticProfile.DEAL_V1_2_INT32, "cap-hash");
        check(context.semanticProfile() == SemanticProfile.DEAL_V1_2_INT32
                && "cap-hash".equals(context.capabilityRegistryHash()),
            "LoweringContext pins the digest input {semanticProfile, capabilityRegistryHash}");
        check(LoweringContext.CANONICAL_JSON_KEYS.equals(List.of("capabilityRegistryHash", "semanticProfile")),
            "the lowering-context canonical JSON object has exactly the two keys in sorted order");

        // ExecutableLoweredProject.
        ProjectInterfaceIndex index = new ProjectInterfaceIndex(ProjectInterfaceIndex.FORMAT_VERSION,
            Map.of(new ModuleId("entry"), new ExternalModuleInterface(new ModuleId("entry"),
                ExternalModuleKind.IMPLEMENTATION, List.of(), List.of(), List.of(),
                InitializationMode.ONCE_AFTER_DEPENDENCIES)));
        ExecutableLoweredProject project = new ExecutableLoweredProject(
            SemanticProfile.DEAL_V1_2_INT32, index, Map.of(new ModuleId("entry"), unit),
            new ModuleId("entry"));
        check(project.modules().get(new ModuleId("entry")) == unit
                && project.entryModule().equals(new ModuleId("entry")),
            "the project carries the complete implementation closure and the entry module");
        expectRejected(() -> new ExecutableLoweredProject(SemanticProfile.LEGACY_SAFE_INT, index,
                Map.of(new ModuleId("entry"), unit), new ModuleId("entry")),
            "a LEGACY_SAFE_INT project cannot be constructed");
        expectRejected(() -> new ExecutableLoweredProject(SemanticProfile.DEAL_V1_2_INT32, index,
                Map.of(new ModuleId("entry"), unit), new ModuleId("other")),
            "the entry module must be present in the closure");
        expectRejected(() -> new ProjectInterfaceIndex("deal.semantic-interface/2", Map.of()),
            "a foreign interface format version is rejected");

        // Interface entries (the F2-pinned shapes: FieldInterface
        // {name, declaredType, optional, nullable, hasDefault},
        // ResolvedImport {alias, modulePath, resolvedModuleId, kind},
        // ExportInterface {name, declaredType}).
        ClassFactoryId ctor = new ClassFactoryId(0);
        ClassInterface classEntry = new ClassInterface(new ClassId("m", "C"),
            List.of(new FieldInterface("f", "int", true, false, true)), ctor);
        ExternalModuleInterface entry = new ExternalModuleInterface(new ModuleId("m"),
            ExternalModuleKind.IMPLEMENTATION,
            List.of(new ResolvedImport("a", "a", new ModuleId("a"),
                ExternalModuleKind.IMPLEMENTATION)),
            List.of(new ExportInterface("x", "int")),
            List.of(classEntry),
            InitializationMode.ONCE_AFTER_DEPENDENCIES);
        check(entry.initialization() == InitializationMode.ONCE_AFTER_DEPENDENCIES
                && entry.classes().get(0).constructionEntry() == ctor
                && entry.imports().get(0).resolvedModuleId().equals(new ModuleId("a"))
                && "int".equals(entry.exports().get(0).declaredType()),
            "ExternalModuleInterface carries imports/exports/classes and ONCE_AFTER_DEPENDENCIES");
    }

    // =========================================================================
    // Package hygiene: deal.semantic.ir stays frontend-free; deal.semantic
    // is the pipeline foundation consuming read-only checker facts (F8)
    // =========================================================================

    static void testPackageHygiene() {
        System.out.println("-- Package hygiene: deal.semantic.ir stays frontend-free; "
            + "deal.semantic consumes read-only checker facts (F8) --");

        // The closed schema package depends only on the JDK (plus the
        // diagnostics registration the failure registry/validator consume):
        // no AST/checker/codegen/module/parser/project/source/IR import.
        List<String> schemaForbidden = List.of(
            "deal.ast", "deal.checker", "deal.codegen", "deal.module", "deal.parser",
            "deal.lexer", "deal.types", "deal.project", "deal.source", "deal.ir",
            "deal.Main");

        // The pipeline foundation (deal.semantic, F8) consumes deal.diagnostics
        // and read-only checker facts (deal.ast/deal.checker/deal.types) plus the
        // closed schema; it must never reach an emitter/target/orchestrator surface.
        List<String> foundationForbidden = List.of(
            "deal.codegen", "deal.module", "deal.parser", "deal.lexer", "deal.project",
            "deal.source", "deal.ir", "deal.Main");

        int scanned = 0;
        scanned += scanImports(Path.of("deal/semantic/ir"), schemaForbidden);
        scanned += scanImports(Path.of("deal/semantic"), foundationForbidden);
        check(scanned > 0, "the package scan examined the deal.semantic sources");
    }

    private static int scanImports(Path dir, List<String> forbiddenPrefixes) {
        int scanned = 0;
        if (!Files.isDirectory(dir)) {
            return scanned;
        }
        try (var stream = Files.list(dir)) {
            for (Path file : stream.filter(p -> p.toString().endsWith(".java")).toList()) {
                for (String line : Files.readAllLines(file)) {
                    String trimmed = line.trim();
                    if (trimmed.startsWith("import ")) {
                        scanned++;
                        String imported = trimmed.substring("import ".length())
                            .replace(";", "").trim();
                        for (String prefix : forbiddenPrefixes) {
                            check(!imported.equals(prefix) && !imported.startsWith(prefix + "."),
                                file.getFileName() + " must not import " + prefix
                                    + " (offending import: " + imported + ")");
                        }
                    }
                }
            }
        } catch (Exception e) {
            fail("package scan failed: " + e);
        }
        return scanned;
    }

    // =========================================================================
    // Main
    // =========================================================================

    public static void main(String[] args) {
        System.out.println("=== Semantic IR Schema Test (ISSUE-0282) ===\n");

        testClosedEnums();
        testReservedNames();
        testConstructTable();
        testRuntimeDescriptorGoldens();
        testSemanticIds();
        testBindingShapes();
        testPayloadConstruction();
        testSemanticOpWiring();
        testCapabilityCatalog();
        testUnitAndProject();
        testPackageHygiene();

        System.out.println("\nPassed: " + passed + ", Failed: " + failed);
        if (failed > 0) {
            System.exit(1);
        }
    }
}
