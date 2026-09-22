package deal.semantic;

import deal.diagnostics.CompilerDiagnostic;

import java.util.List;
import java.util.Objects;

/**
 * The outcome of one {@link MigrationPlanner#planRoutes} call
 * (foundation F4): on success exactly one immutable
 * {@link ModuleRoutePlan} per target with an empty diagnostics list; on
 * a plan-time E6005 fact defect the plan is {@code null} and the
 * diagnostics list carries the single E6005 produced through the failure
 * contract registry (T5) with the prescribed
 * {@code LoweringFailureDetail} payload — never a crash, never a silent
 * reroute for a fact defect. SHARED-ineligibility — {@code
 * LEGACY_SAFE_INT} profile, {@code PUBLIC_BUILD + PRE_ACTIVATION},
 * {@code STDLIB_TIME_CONFLICT} (the inert marker no manifest claims
 * since K7), or a required
 * capability not {@code PROMOTED} for the target — reroutes LEGACY at
 * plan time with zero diagnostics: never an error, never a within-run
 * fallback.
 *
 * @param plan        the target route plan; null exactly when planning
 *                    failed
 * @param diagnostics the E6005 diagnostics (empty on success); non-null
 */
public record RoutePlanResult(
    ModuleRoutePlan plan,
    List<CompilerDiagnostic> diagnostics
) {

    public RoutePlanResult {
        Objects.requireNonNull(diagnostics, "diagnostics must not be null");
        diagnostics = List.copyOf(diagnostics);
        if (plan == null && diagnostics.isEmpty()) {
            throw new IllegalArgumentException(
                "a failed route plan carries at least one diagnostic");
        }
        if (plan != null && !diagnostics.isEmpty()) {
            throw new IllegalArgumentException(
                "a successful route plan carries no diagnostics");
        }
    }

    /** Whether planning failed (at least one E6005 diagnostic). */
    public boolean hasErrors() {
        return !diagnostics.isEmpty();
    }
}
