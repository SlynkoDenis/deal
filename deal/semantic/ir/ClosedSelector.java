package deal.semantic.ir;

/**
 * The closed selector family carried by an
 * {@link OperationContractSnapshot}'s optional {@code selector} field
 * (S2): exactly a {@link UnarySelector}, a {@link BinarySelector}, or a
 * {@link StdlibFunctionId} (stdlib ids are the standard-library selector
 * names, {@code TIME_NOW_MILLIS} included since K7).
 *
 * <p>Closed sealed family; no other selector shape exists. The intrinsic
 * conversions ({@code INT_CONVERT}/{@code NUMBER_CONVERT}) and control
 * selectors are payload fields, not snapshot selectors (parent closed
 * operation table).</p>
 */
public sealed interface ClosedSelector
    permits UnarySelector, BinarySelector, StdlibFunctionId {
}
