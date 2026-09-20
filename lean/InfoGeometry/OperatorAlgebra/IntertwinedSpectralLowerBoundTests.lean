import InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound
import InfoGeometry.Automorphic.CuspidalSpectralLowerBound
import InfoGeometry.Detector.AmariHessianDuality

open InfoGeometry.OperatorAlgebra.IntertwinedSpectralLowerBound
open InfoGeometry.Detector.AmariHessianDuality

example : (1 / 4 : ℝ) ≤ 1 / 2 := by
  apply eigenvalue_ge_of_quadratic_bound
    ((1 / 2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) (1 / 4)
    ?_ (vector := (1 : ℝ)) (by norm_num) rfl
  intro vector
  change (1 / 4 : ℝ) * inner ℝ vector vector ≤
    inner ℝ vector ((1 / 2 : ℝ) • vector)
  rw [real_inner_smul_right]
  nlinarith [inner_self_nonneg (𝕜 := ℝ) (x := vector)]

example : fisher_metric 1 (1 / 2) = 1 / 4 ∧
    ∃ operator : ℝ →ₗ[ℝ] ℝ,
      operator.HasEigenvalue (3 / 16 : ℝ) ∧ (3 / 16 : ℝ) < 1 / 4 := by
  constructor
  · convert maximum_fisher_info_at_summit 1 (by norm_num) using 1 <;> norm_num
  · let operator : ℝ →ₗ[ℝ] ℝ := (3 / 16 : ℝ) • LinearMap.id
    have eigen : operator.HasEigenvector (3 / 16 : ℝ) 1 := by
      exact ⟨Module.End.mem_eigenspace_iff.mpr rfl, by norm_num⟩
    exact ⟨operator, Module.End.hasEigenvalue_of_hasEigenvector eigen, by norm_num⟩

example :
    (0 : ℝ →ₗ[ℝ] ℝ).comp ((3 / 16 : ℝ) • LinearMap.id) =
      ((1 / 4 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp 0 := by
  ext vector
  simp

#print axioms eigenvalue_ge_of_quadratic_bound
#print axioms lower_bound_of_intertwining
#print axioms deviation_eq_zero_of_quarter_bound
#print axioms InfoGeometry.Automorphic.CuspidalSpectralLowerBound.cuspidal_eigenspace_eq_bot_below_bound
