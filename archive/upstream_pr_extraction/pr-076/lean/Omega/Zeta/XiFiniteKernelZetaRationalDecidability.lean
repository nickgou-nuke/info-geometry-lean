import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.DynZeta

namespace Omega.Zeta

/-- Concrete finite-kernel rationality owner: the golden-mean Fredholm
determinant is the displayed quadratic polynomial. -/
theorem paper_xi_finite_kernel_zeta_rational_decidability :
    ∀ z : ℤ, (fredholmGoldenMean z).det = 1 - z - z ^ 2 := by
  exact paper_finite_zeta_periodicity_witness.1

end Omega.Zeta
