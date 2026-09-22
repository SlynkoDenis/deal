package deal.semantic.ir;

import java.util.List;

/**
 * The closed source-construct coverage table of
 * {@code deal.semantic-ir/1} (parent "Source-construct coverage"; schema
 * S4) — reproduced verbatim, exactly the parent page's 23 rows. The
 * parent section is normative and this set never diverges from it.
 *
 * <p>Each of the 23 rows carries a required common form recorded
 * verbatim ({@link #requiredCommonForm()}) together with its mapped
 * op-kind set ({@link #mappedOpKinds()}, the kinds named by the pinned
 * detector row) — the data {@code constructCoverage} obligations consume:
 * a construct recorded in a unit's {@code constructCoverage} must have at
 * least one produced op of a mapped kind (validator R-COVERAGE). The
 * detector rows cover every reachable checked AST kind: {@code call} and
 * {@code cross-module call} cover {@code CallExpr}, {@code
 * unary/arithmetic/comparison} covers {@code UnaryExpr}/{@code BinaryExpr},
 * and {@code function declaration/expression} covers
 * {@code FunctionDeclaration}/{@code FunctionExpr} — so every
 * {@code CALL}/{@code UNARY}/{@code BINARY}/{@code CLOSURE_NEW}/
 * {@code FUNCTION_ADAPT}/{@code RECURSIVE_GROUP_INIT} op has a producing
 * construct. ISSUE-0231..0239 extend only the construct→op detector rows
 * (the precise per-construct op production within these fixed rows), never
 * this closed {@code ConstructKind} set.</p>
 *
 * <p>The {@code std/time.nowMillis} row carries its required common form
 * and op-kind set since K7: the construct is the recognized cataloged
 * call through the closed {@code std.time}/{@code nowMillis} row, it
 * lowers to {@code STDLIB_CALL(TIME_NOW_MILLIS)} with the declared
 * {@code int} return boundary ({@code STDLIB_RETURN}) as its single
 * terminal, and it is recorded in {@code constructCoverage} like every
 * other construct (a data-level constraint enforced at
 * {@link LoweredModuleUnit} construction).</p>
 */
public enum ConstructKind {

    /** Required common form: {@code CONST}. */
    SCALAR_LITERAL("CONST", List.of(SemanticOpKind.CONST)),

    /** Required common form: {@code BINDING_LOAD}, intrinsic binding, or explicit import/export reference. */
    IDENTIFIER("BINDING_LOAD, intrinsic binding, or explicit import/export reference",
        List.of(SemanticOpKind.BINDING_LOAD, SemanticOpKind.INTRINSIC_CALL, SemanticOpKind.EXPORT_READ)),

    /** Required common form: {@code UNARY}/{@code BINARY}; logical operators use selector-bearing {@code BRANCH}. */
    UNARY_ARITHMETIC_COMPARISON("UNARY/BINARY; logical operators use selector-bearing BRANCH",
        List.of(SemanticOpKind.UNARY, SemanticOpKind.BINARY, SemanticOpKind.BRANCH)),

    /** Required common form: {@code STRING_CONCAT} with every fragment/interpolation in source order. */
    STRING_CONCAT_TEMPLATE("STRING_CONCAT with every fragment/interpolation in source order",
        List.of(SemanticOpKind.STRING_CONCAT)),

    /** Required common form: {@code CALL} (DIRECT/INDIRECT with execution-binding resolution),
     * {@code CALLBACK_INVOKE}, {@code INTRINSIC_CALL}, {@code STDLIB_CALL}, or
     * {@code ASYNC_START}+{@code AWAIT}. */
    CALL("CALL (DIRECT/INDIRECT with execution-binding resolution), CALLBACK_INVOKE, "
        + "INTRINSIC_CALL, STDLIB_CALL, or ASYNC_START+AWAIT",
        List.of(SemanticOpKind.CALL, SemanticOpKind.CALLBACK_INVOKE, SemanticOpKind.INTRINSIC_CALL,
            SemanticOpKind.STDLIB_CALL, SemanticOpKind.ASYNC_START, SemanticOpKind.AWAIT)),

    /** Required common form: {@code CALL(EXTERNAL)}/{@code ASYNC_START(EXTERNAL)} with
     * {@code EXTERNAL_ENTRY} on the shared-body callee side, or the retained ABI path. */
    CROSS_MODULE_CALL("CALL(EXTERNAL)/ASYNC_START(EXTERNAL) with EXTERNAL_ENTRY on the "
        + "shared-body callee side, or the retained ABI path",
        List.of(SemanticOpKind.CALL, SemanticOpKind.ASYNC_START, SemanticOpKind.EXTERNAL_ENTRY)),

    /** Required common form: {@code ARRAY_LENGTH}, {@code FIELD_READ}, {@code MEMBER_READ},
     * or {@code EXPORT_READ} from checked type/symbol. */
    MEMBER_ACCESS("ARRAY_LENGTH, FIELD_READ, MEMBER_READ, or EXPORT_READ from checked type/symbol",
        List.of(SemanticOpKind.ARRAY_LENGTH, SemanticOpKind.FIELD_READ, SemanticOpKind.MEMBER_READ,
            SemanticOpKind.EXPORT_READ)),

    /** Required common form: {@code INDEX_NORMALIZE}, {@code INDEX_READ}
     * ({@code ARRAY_ELEMENT_READ} boundary), contextual {@code BOUNDARY}. */
    INDEX_ACCESS("INDEX_NORMALIZE, INDEX_READ (ARRAY_ELEMENT_READ boundary), contextual BOUNDARY",
        List.of(SemanticOpKind.INDEX_NORMALIZE, SemanticOpKind.INDEX_READ, SemanticOpKind.BOUNDARY)),

    /** Required common form: {@code ARRAY_NEW} ({@code ARRAY_LITERAL_ELEMENT} boundaries), {@code TABLE_NEW}. */
    ARRAY_OBJECT_LITERAL("ARRAY_NEW (ARRAY_LITERAL_ELEMENT boundaries), TABLE_NEW",
        List.of(SemanticOpKind.ARRAY_NEW, SemanticOpKind.TABLE_NEW)),

    /** Required common form: {@code CLASS_NEW} (local and imported); imported defaults via
     * the owner's {@code CLASS_FACTORY} or the retained ABI. */
    CLASS_OBJECT_LITERAL("CLASS_NEW (local and imported); imported defaults via the owner's "
        + "CLASS_FACTORY or the retained ABI",
        List.of(SemanticOpKind.CLASS_NEW, SemanticOpKind.CLASS_FACTORY)),

    /** Required common form: {@code CLOSURE_NEW}/{@code RECURSIVE_GROUP_INIT} and a
     * {@code LoweredFunction}; adaptation explicit via {@code FUNCTION_ADAPT} (D15). */
    FUNCTION_DECLARATION_EXPRESSION("CLOSURE_NEW/RECURSIVE_GROUP_INIT and a LoweredFunction; "
        + "adaptation explicit via FUNCTION_ADAPT (D15)",
        List.of(SemanticOpKind.CLOSURE_NEW, SemanticOpKind.RECURSIVE_GROUP_INIT,
            SemanticOpKind.FUNCTION_ADAPT)),

    /** Required common form: {@code ASSIGN} address chain (D14): receiver → key → RHS →
     * normalize → write check ({@code ARRAY_ELEMENT_ASSIGNMENT}) → commit. */
    ASSIGNMENT("ASSIGN address chain (D14): receiver \u2192 key \u2192 RHS \u2192 normalize "
        + "\u2192 write check (ARRAY_ELEMENT_ASSIGNMENT) \u2192 commit",
        List.of(SemanticOpKind.ASSIGN)),

    /** Required common form: {@code DELETE} address chain (D14): receiver → key → normalize →
     * [array bounds boundary ({@code ARRAY_ELEMENT_DELETE})] → commit. */
    DELETE("DELETE address chain (D14): receiver \u2192 key \u2192 normalize \u2192 "
        + "[array bounds boundary (ARRAY_ELEMENT_DELETE)] \u2192 commit",
        List.of(SemanticOpKind.DELETE)),

    /** Required common form: {@code HAS_FIELD} on a checked receiver/key, evaluated once each. */
    HAS("HAS_FIELD on a checked receiver/key, evaluated once each",
        List.of(SemanticOpKind.HAS_FIELD)),

    /** Required common form: {@code ASYNC_START} (binding-resolved:
     * {@code DEAL_BODY}/{@code HOST}/{@code EXTERNAL}), {@code AWAIT} per D13. */
    AWAIT_ASYNC_CALL("ASYNC_START (binding-resolved: DEAL_BODY/HOST/EXTERNAL), AWAIT per D13",
        List.of(SemanticOpKind.ASYNC_START, SemanticOpKind.AWAIT)),

    /** Required common form: allocation, initializer, boundary, initialization. */
    VARIABLE_DECLARATION("allocation, initializer, boundary, initialization",
        List.of(SemanticOpKind.BINDING_ALLOC, SemanticOpKind.BINDING_INIT, SemanticOpKind.BOUNDARY)),

    /** Required common form: {@code RETURN} (D13) or {@code DISCARD}. */
    RETURN_EXPRESSION_STATEMENT("RETURN (D13) or DISCARD",
        List.of(SemanticOpKind.RETURN, SemanticOpKind.DISCARD)),

    /** Required common form: {@code BRANCH}, {@code LOOP}, or {@code FOR_EACH}. */
    IF_WHILE_FOR_FOR_OF("BRANCH, LOOP, or FOR_EACH",
        List.of(SemanticOpKind.BRANCH, SemanticOpKind.LOOP, SemanticOpKind.FOR_EACH)),

    /** Required common form: matching loop-ID transfer. */
    BREAK_CONTINUE("matching loop-ID transfer",
        List.of(SemanticOpKind.BREAK, SemanticOpKind.CONTINUE)),

    /** Required common form: {@code TRY_CATCH}, {@code THROW}. */
    TRY_CATCH_THROW("TRY_CATCH, THROW",
        List.of(SemanticOpKind.TRY_CATCH, SemanticOpKind.THROW)),

    /** Required common form: layout, defaults, factory, and export metadata.
     * The ISSUE-0231..0239 row-extension authority admits the layout-only
     * production of this row: a class layout is unit data
     * ({@code unit.classLayouts}), never an op, so a no-default
     * non-exported class produces no op of the mapped kinds and the row's
     * R-COVERAGE obligation is satisfied by the produced layout record —
     * the op-bearing shapes (defaulted/exported classes) evidence the row
     * through the produced {@code CLASS_DEFAULT}/{@code CLASS_FACTORY}
     * ops, and no vacuous op is invented. */
    CLASS_DECLARATION("layout, defaults, factory, and export metadata",
        List.of(SemanticOpKind.CLASS_DEFAULT, SemanticOpKind.CLASS_FACTORY,
            SemanticOpKind.EXPORT_PUBLISH)),

    /** Required common form: module/import/export/entry operations plus interface/ABI records. */
    IMPORT_EXPORT_ENTRY("module/import/export/entry operations plus interface/ABI records",
        List.of(SemanticOpKind.MODULE_INIT, SemanticOpKind.MODULE_IMPORT, SemanticOpKind.EXPORT_READ,
            SemanticOpKind.EXPORT_PUBLISH, SemanticOpKind.ENTRY_INVOKE)),

    /**
     * Required common form: {@code STDLIB_CALL(TIME_NOW_MILLIS)} with the
     * declared {@code int} return boundary and its {@code INT32_RESULT}
     * terminal — the recognized cataloged call through the closed
     * {@code std.time}/{@code nowMillis} row (K7).
     */
    STDLIB_TIME_NOW_MILLIS("STDLIB_CALL(TIME_NOW_MILLIS) with the declared int "
        + "return boundary and its INT32_RESULT terminal",
        List.of(SemanticOpKind.STDLIB_CALL, SemanticOpKind.BOUNDARY));

    private final String requiredCommonForm;
    private final List<SemanticOpKind> mappedOpKinds;

    ConstructKind(String requiredCommonForm, List<SemanticOpKind> mappedOpKinds) {
        this.requiredCommonForm = requiredCommonForm;
        this.mappedOpKinds = List.copyOf(mappedOpKinds);
    }

    /**
     * The verbatim required common form of this construct row, or
     * {@code null} when the row carries none (no row does since K7; the
     * accessor keeps the closed-table shape).
     */
    public String requiredCommonForm() {
        return requiredCommonForm;
    }

    /**
     * The mapped op-kind set of this construct row — the kinds named by
     * the pinned detector row. R-COVERAGE requires at least one
     * produced op of a mapped kind per recorded construct.
     */
    public List<SemanticOpKind> mappedOpKinds() {
        return mappedOpKinds;
    }
}
