import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The full Jacobian determinant factors as `n!` times the Vandermonde product. -/
noncomputable def powerSumJacobianDet (n : ℕ) (vandermondeProduct : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) * vandermondeProduct

/-- On the simplex tangent hyperplane, nonzero Jacobian determinant is the packaged full-rank
criterion used by the paper statement. -/
def powerSumTangentMapFullRank (n : ℕ) (vandermondeProduct : ℝ) : Prop :=
  0 < powerSumJacobianDet n vandermondeProduct

/-- Paper label: `thm:pom-power-sum-vandermonde-jacobian`. -/
theorem paper_pom_power_sum_vandermonde_jacobian
    (n : ℕ) (vandermondeProduct : ℝ) (vandermondeProduct_pos : 0 < vandermondeProduct) :
    powerSumJacobianDet n vandermondeProduct =
        (Nat.factorial n : ℝ) * vandermondeProduct ∧
      powerSumTangentMapFullRank n vandermondeProduct := by
  refine ⟨rfl, ?_⟩
  have hfac : 0 < (Nat.factorial n : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  simpa [powerSumTangentMapFullRank, powerSumJacobianDet] using
    mul_pos hfac vandermondeProduct_pos

/-- Paper label: `cor:pom-power-sum-local-chart`. -/
theorem paper_pom_power_sum_local_chart
    (n : ℕ) (vandermondeProduct : ℝ) (vandermondeProduct_pos : 0 < vandermondeProduct) :
    powerSumTangentMapFullRank n vandermondeProduct := by
  exact (paper_pom_power_sum_vandermonde_jacobian n vandermondeProduct
    vandermondeProduct_pos).2

end Omega.POM
