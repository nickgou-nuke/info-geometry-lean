import InfoGeometry.Algebra.LieCyclotomicBridge

noncomputable section

namespace InfoGeometry.Algebra.CubicCompanionFlow

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Algebra.LieCyclotomicBridge
open InfoGeometry.Physics.HestenesKreinOperatorCalculus
open scoped Matrix.Norms.Operator

def generator : Mat2 :=
  (Real.sqrt 3)⁻¹ • ((2 : ℝ) • thirdRoot + 1)

theorem generator_sq : generator ^ 2 = -1 := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hnonzero : Real.sqrt 3 ≠ 0 := by positivity
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [generator, thirdRoot, pow_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> field_simp <;> nlinarith

theorem exp_generator :
    NormedSpace.exp ((2 * Real.pi / 3) • generator) = thirdRoot := by
  have hangle : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  have hcos : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [hangle, Real.cos_sub]
    simp [Real.cos_pi_div_three]
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [hangle, Real.sin_sub]
    simp [Real.sin_pi_div_three]
  have hnonzero : Real.sqrt 3 ≠ 0 := by positivity
  rw [exp_of_sq_eq_neg_one generator generator_sq, hcos, hsin]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [generator, thirdRoot] <;> field_simp <;> ring

theorem thirdRoot_not_orthogonal : thirdRoot.transpose * thirdRoot ≠ 1 := by
  intro hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 1 1) hequal
  norm_num [thirdRoot, Matrix.mul_apply, Fin.sum_univ_two] at hentry

end InfoGeometry.Algebra.CubicCompanionFlow
