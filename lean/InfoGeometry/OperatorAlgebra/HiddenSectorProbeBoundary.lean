import InfoGeometry.OperatorAlgebra.PO55RicciFlux
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Linear probe boundary for a hidden grade

This file isolates the exact algebraic consequence of a linear observable
being insensitive to a supplied positive TKK grade.  It does not construct an
electromagnetic probe and does not identify any grade with dark matter.
-/

namespace InfoGeometry.OperatorAlgebra

namespace TKKLieClosure

variable
    {J L E : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup E] [Module ℝ E]
    (T : TKKLieClosure J L)

/--
If a linear probe has the same value on a positive-grade element as on zero,
then it annihilates that positive-grade element.  The linearity hypothesis is
what turns the readout equality used by `HiddenInertiaReadout` into a genuine
zero statement.
-/
theorem linear_probe_pos_eq_zero_of_readout
    (probe : L →ₗ[ℝ] E)
    (h_readout : ∀ x : J, probe (T.pos x) = probe 0) (x : J) :
    probe (T.pos x) = 0 := by
  rw [h_readout x, map_zero]

end TKKLieClosure

end InfoGeometry.OperatorAlgebra
