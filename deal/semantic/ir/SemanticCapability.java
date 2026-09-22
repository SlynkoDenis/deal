package deal.semantic.ir;

/**
 * The closed semantic capability set of the common lowering layer
 * (foundation F3/F7; schema S4 capability catalog).
 *
 * <p>Closed set — exactly the twelve values below in the pinned S4
 * capability order; no open or unknown fallback member and no external
 * extension point exist. The declaration order is normative: the release
 * capability registry orders its canonical JSON entries by capability in
 * exactly this order ({@code capabilityRegistryHash} = SHA-256 of the
 * canonical JSON over the ordered capability × target cross product).
 * {@link #STDLIB_TIME_CONFLICT} is an inert routing marker since K7: the
 * superseded four-part line trigger and its planning claim are retired
 * ({@code semantic-ir-construct-coverage-cutover} K7 item 6), no manifest
 * claims it, and the member stays in the closed set as the closed-set
 * surface the capability catalog, the planner's reroute, and the
 * validator's empty-evidence rule consume.</p>
 */
public enum SemanticCapability {

    /** Core value kinds and their operations (CONST, UNARY, BINARY, STRING_CONCAT). */
    FOUNDATION_VALUES,

    /** Signed-32-bit integer semantics and conversion/boundary operations. */
    SIGNED_INT32,

    /** Array/table/string containers, members, indexes, optionals, has, for-of. */
    CONTAINERS_AND_STRINGS,

    /** Structural descriptors of declared types. */
    DESCRIPTORS,

    /** Explicit boundary operations over the closed boundary-assignment table. */
    BOUNDARIES,

    /** Evaluation order, branches, loops, and discards. */
    EVALUATION_ORDER,

    /** Bindings, allocations, recursive groups, and closure creation. */
    BINDINGS,

    /** Calls, callbacks, external entries, async start/await, return, entry invoke. */
    CALLS,

    /** Standard-library algorithm calls over the closed stdlib table. */
    STDLIB_SEMANTICS,

    /** Inert routing marker (superseded D8 claim): never claimed nor lowered (K7). */
    STDLIB_TIME_CONFLICT,

    /** Classes, class factories/defaults, fields, and JSON class conversions. */
    CLASSES,

    /** Module init/import and export read/publish operations. */
    MODULES
}
