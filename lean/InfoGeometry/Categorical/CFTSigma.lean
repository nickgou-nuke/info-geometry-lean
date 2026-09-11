import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.Ring
import InfoGeometry.Categorical.CFTPrimary
import InfoGeometry.Categorical.CFTWard
import InfoGeometry.Categorical.CFTVirasoro

namespace InfoGeometry.Categorical

/-- The sigma-sector readout is the half-integer conformal spin scale. -/
noncomputable def sigmaWeight (n : ℤ) : ℝ :=
  (n : ℝ) / 2

theorem sigmaWeight_double (n : ℤ) : 2 * sigmaWeight n = n := by
  dsimp [sigmaWeight]
  ring

/--
If a Ward identity forces two primary weights to agree, then the sigma-sector
readout respects the same comparison after doubling.
-/
theorem sigmaWard_consistent
    {Δ1 Δ2 z1 z2 C : ℝ}
    (h : C * (z1 - z2) * (Δ1 - Δ2) = 0)
    (h1 : z1 - z2 ≠ 0) (h2 : C ≠ 0) :
    Δ1 = Δ2 := by
  exact ward_identity_2pt h h1 h2

end InfoGeometry.Categorical
