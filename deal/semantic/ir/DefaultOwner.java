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
 * execution, emission, and default-evaluation consumer keeps rejecting
 * them as fail-closed producer defects until the construction children
 * realize them — a registration fact is never silently executed as
 * another owner. {@code RETAINED_ABI} keeps its own never-produced
 * rejection (the retained route does not exist on the production path).</p>
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
     * {@code <C>_defaults} entry (registration fact; the host-construction
     * execution is not realized in this slice).
     */
    HOST_DEFAULTS,

    /**
     * An extern-C declaration class's defaults are the loaded module's
     * validated {@code <C>_plan} entry (registration fact; the
     * C-struct-construction execution is not realized in this slice).
     */
    FFI_PLAN,

    /**
     * The builtin {@code Error} class's constant empty-string defaults
     * (registration fact; the builtin-Error construction execution is not
     * realized in this slice).
     */
    BUILTIN_DEFAULTS
}
