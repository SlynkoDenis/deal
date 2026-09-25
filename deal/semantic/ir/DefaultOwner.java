package deal.semantic.ir;

/**
 * The closed default-ownership set of class construction (parent D16;
 * schema S3; extended by {@code project-lowering-entry-and-registration-seeds}
 * D5 and {@code semantic-ir-construct-coverage-cutover} K9 items 3 and 6):
 * who fills defaults for omitted required-present fields of a constructed
 * class.
 *
 * <p>Closed set — exactly {@link #LOCAL}, {@link #SHARED_FACTORY},
 * {@link #RETAINED_ABI}, {@link #HOST_DEFAULTS}, {@link #FFI_PLAN}, and
 * {@link #BUILTIN_DEFAULTS}; no open or unknown fallback member and no
 * external extension point exist. {@code LOCAL} runs {@code CLASS_DEFAULT}
 * children in declaration order inside the caller's {@code CLASS_NEW};
 * {@code SHARED_FACTORY} transfers to the owner module's
 * {@code CLASS_FACTORY} op; {@code RETAINED_ABI} transfers through the
 * {@code TargetModuleAbi} factory entry (no common default ops). Defaults
 * evaluate per construction in the declaring module's scope.</p>
 *
 * <p><b>The three registration-owned members (ISSUE-0631).</b>
 * {@link #HOST_DEFAULTS}, {@link #FFI_PLAN}, and {@link #BUILTIN_DEFAULTS}
 * are the project lowering's class registration seeds: they name where a
 * declared class's omitted defaults live ({@code HOST_DEFAULTS}: the
 * loaded host module's {@code <C>_defaults} entry; {@code FFI_PLAN}: the
 * loaded extern-C module's validated {@code <C>_plan} entry;
 * {@code BUILTIN_DEFAULTS}: the builtin {@code Error} class's constant
 * empty-string defaults). The seeds register these members as facts; every
 * consumer resolves an unrecognized or unrealized owner as a fail-closed
 * producer defect — a registration fact is never silently executed as
 * another owner. {@code HOST_DEFAULTS} is realized by the host
 * declaration class construction (ISSUE-0624),
 * {@code BUILTIN_DEFAULTS} by the builtin {@code Error} construction
 * (ISSUE-0619), and {@code FFI_PLAN} by the extern-C C-struct
 * construction (ISSUE-0666: the provided fields' boundaries, the
 * deterministic extra-key guard, and the runtime's four phases over the
 * loaded {@code <C>_plan} entry). {@code RETAINED_ABI} keeps its own
 * never-produced rejection (the retained route does not exist on the
 * production path).</p>
 */
public enum DefaultOwner {

    /** Defaults are applied locally by the constructing {@code CLASS_NEW}. */
    LOCAL,

    /** Defaults transfer to the shared owner module's {@code CLASS_FACTORY}. */
    SHARED_FACTORY,

    /** Defaults transfer through the retained target ABI factory entry. */
    RETAINED_ABI,

    /**
     * A host declaration class's defaults are the loaded host module's
     * {@code <C>_defaults} entry (ISSUE-0624; realized by the host
     * declaration class construction: the loaded defaults are deep-copied
     * per attempt, the provided overlay raises the E8007 extra-key
     * projection, the omitted optional sentinels are removed, and the
     * instance is tagged with the canonical class identity).
     */
    HOST_DEFAULTS,

    /**
     * An extern-C declaration class's defaults are the loaded module's
     * validated {@code <C>_plan} entry (ISSUE-0666; realized by the
     * C-struct construction: the provided fields cross their
     * {@code CLASS_LITERAL_FIELD} boundaries in declaration order, the
     * deterministic extra-key guard raises the E8007 projection at the
     * literal origin, and {@code __rt.class_plan_} runs the plan's phase-1
     * copy, its omitted fields' deferred evaluators exactly once per
     * attempt in class source order, its per-field descriptor validation,
     * and its identity tag and publication).
     */
    FFI_PLAN,

    /**
     * The builtin {@code Error} class's constant empty-string defaults
     * (registration fact; the builtin-Error construction execution is not
     * realized in this slice).
     */
    BUILTIN_DEFAULTS
}
