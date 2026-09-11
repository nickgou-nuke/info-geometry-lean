import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Antiunitary Kramers involution on ℂ²

The standard two-dimensional complex Hilbert space equipped with the
conjugate-linear time-reversal operator `𝓣` satisfying:

* `𝓣² = -𝟙` (quaternionic square);
* `⟪𝓣 u, 𝓣 v⟫ = ⟪v, u⟫` (antiunitary inner-product reversal);
* `⟪v, 𝓣 v⟫ = 0` for all `v` (strict Kramers orthogonality).

These algebraic facts force every eigenspace of any `𝓣`-invariant
Hamiltonian to have even dimension.
-/

namespace InfoGeometry.Quantum.AntiunitaryKramers

open Complex

/-- The standard two-dimensional complex Hilbert space. -/
abbrev H2 := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- Conjugate-semilinear time-reversal map on `H2`. -/
def timeReversal (v : H2) : H2 :=
  ![-star (v 1), star (v 0)]

theorem timeReversal_add (u v : H2) :
    timeReversal (u + v) = timeReversal u + timeReversal v := by
  funext i
  fin_cases i <;> simp [timeReversal]
  ring

theorem timeReversal_smul_conj (c : ℂ) (v : H2) :
    timeReversal (c • v) = (star c) • timeReversal v := by
  funext i
  fin_cases i <;> simp [timeReversal]
  try ring

theorem timeReversal_sq_neg_one (v : H2) :
    timeReversal (timeReversal v) = -v := by
  funext i
  fin_cases i <;> simp [timeReversal]
  try ring

theorem timeReversal_kramers_ortho (v : H2) :
    (star (v 0) * (timeReversal v 0) + star (v 1) * (timeReversal v 1)) = 0 := by
  simp [timeReversal]
  ring

end InfoGeometry.Quantum.AntiunitaryKramers
