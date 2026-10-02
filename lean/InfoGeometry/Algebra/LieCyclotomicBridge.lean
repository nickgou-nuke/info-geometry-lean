import InfoGeometry.Algebra.MatrixCyclotomics
import InfoGeometry.Physics.HestenesKreinOperatorCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

namespace InfoGeometry.Algebra.LieCyclotomicBridge

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.GrandUnification.Matrix2KANPauliChain
open InfoGeometry.Algebra.MatrixCyclotomics
open scoped Matrix.Norms.Operator

def fourthRoot : Mat2 := -Eminus

def thirdRoot : Mat2 := !![0, -1; 1, -1]

theorem fourthRoot_square : fourthRoot ^ 2 = -1 := by
  rw [fourthRoot, pow_two, neg_mul_neg, Eminus_sq]
  simp

theorem fourthRoot_aeval :
    Polynomial.aeval fourthRoot (Polynomial.cyclotomic 4 ℝ) = 0 := by
  rw [aeval_cyclotomic_four, fourthRoot_square, neg_add_cancel]

theorem thirdRoot_aeval :
    Polynomial.aeval thirdRoot (Polynomial.cyclotomic 3 ℝ) = 0 := by
  rw [Polynomial.cyclotomic_three]
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [thirdRoot, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem thirdRoot_pow_three : thirdRoot ^ 3 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [thirdRoot, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

theorem thirdRoot_order : orderOf thirdRoot = 3 := by
  apply (orderOf_eq_iff (by norm_num : 0 < (3 : ℕ))).mpr
  refine ⟨thirdRoot_pow_three, ?_⟩
  intro exponent hupper hlower hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
  interval_cases exponent <;>
    norm_num [thirdRoot, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at hentry

theorem fourthRoot_pow_four : fourthRoot ^ 4 = 1 := by
  calc
    fourthRoot ^ 4 = (fourthRoot ^ 2) ^ 2 := by rw [← pow_mul]
    _ = 1 := by rw [fourthRoot_square]; simp

theorem fourthRoot_order : orderOf fourthRoot = 4 := by
  apply (orderOf_eq_iff (by norm_num : 0 < (4 : ℕ))).mpr
  refine ⟨fourthRoot_pow_four, ?_⟩
  intro exponent hupper hlower hequal
  have hentry := congrArg (fun matrix : Mat2 => matrix 0 0) hequal
  interval_cases exponent <;>
    norm_num [fourthRoot, Eminus, pow_succ, Matrix.mul_apply, Fin.sum_univ_two] at hentry

theorem rotation_add (first second : ℝ) :
    KPart (first + second) = KPart first * KPart second := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [KPart, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rotation_eq_scalar_combination (angle : ℝ) :
    KPart angle = Real.cos angle • (1 : Mat2) + Real.sin angle • fourthRoot := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [KPart, fourthRoot, Eminus]

theorem exp_fourthRoot (angle : ℝ) :
    NormedSpace.exp (angle • fourthRoot) = KPart angle := by
  rw [InfoGeometry.Physics.HestenesKreinOperatorCalculus.exp_of_sq_eq_neg_one
    fourthRoot fourthRoot_square, ← rotation_eq_scalar_combination]

theorem rotation_pi_half : KPart (Real.pi / 2) = fourthRoot := by
  rw [rotation_eq_scalar_combination]
  simp

theorem exp_pi_half_fourthRoot :
    NormedSpace.exp ((Real.pi / 2) • fourthRoot) = fourthRoot := by
  rw [exp_fourthRoot, rotation_pi_half]

end InfoGeometry.Algebra.LieCyclotomicBridge
