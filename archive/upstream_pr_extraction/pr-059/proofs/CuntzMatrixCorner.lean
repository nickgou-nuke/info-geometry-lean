import Mathlib
import proofs.CuntzEndomorphism

noncomputable section

open Matrix

namespace CuntzMatrixCorner

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Nontrivial A] [NoZeroSMulDivisors ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

/-- 1. Cuntz Matrix Units
  e_{ij} = S_i S_j^*
-/
def cuntzMatrixUnit (i j : Fin 2) : A :=
  S i * star (S j)

theorem cuntzMatrixUnit_mul (i j k l : Fin 2) :
    cuntzMatrixUnit S i j * cuntzMatrixUnit S k l =
      if j = k then cuntzMatrixUnit S i l else 0 := by
  dsimp [cuntzMatrixUnit]
  rw [mul_assoc, ← mul_assoc (star (S j))]
  match j, k with
  | 0, 0 => simp [hC.isom₁]
  | 0, 1 => simp [hC.ortho₁₂]
  | 1, 0 => simp [hC.ortho₂₁]
  | 1, 1 => simp [hC.isom₂]

theorem star_cuntzMatrixUnit (i j : Fin 2) :
    star (cuntzMatrixUnit S i j) = cuntzMatrixUnit S j i := by
  dsimp [cuntzMatrixUnit]
  simp

theorem cuntzMatrixUnit_diagonal_sum :
    cuntzMatrixUnit S 0 0 + cuntzMatrixUnit S 1 1 = 1 := by
  dsimp [cuntzMatrixUnit]
  exact hC.cuntz_sum

/-- 2. Corner map from M_2(C) into O_2 
  Φ(M) = ∑ M_{ij} e_{ij}
-/
def cuntzCornerMap (M : Matrix (Fin 2) (Fin 2) ℂ) : A :=
  (M 0 0) • cuntzMatrixUnit S 0 0 +
  (M 0 1) • cuntzMatrixUnit S 0 1 +
  (M 1 0) • cuntzMatrixUnit S 1 0 +
  (M 1 1) • cuntzMatrixUnit S 1 1

theorem cuntzCornerMap_add (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    cuntzCornerMap S (M + N) = cuntzCornerMap S M + cuntzCornerMap S N := by
  dsimp [cuntzCornerMap, Matrix.add_apply]
  simp [add_smul]
  abel

theorem cuntzCornerMap_one :
    cuntzCornerMap S 1 = 1 := by
  dsimp [cuntzCornerMap, Matrix.one_apply]
  simp
  exact cuntzMatrixUnit_diagonal_sum S

theorem cuntzCornerMap_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) :
    cuntzCornerMap S (M * N) = cuntzCornerMap S M * cuntzCornerMap S N := by
  dsimp [cuntzCornerMap, Matrix.mul_apply, Fin.sum_univ_two]
  simp [add_mul, mul_add, smul_add, add_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, cuntzMatrixUnit_mul, smul_smul, mul_comm]
  abel

theorem cuntzCornerMap_star (M : Matrix (Fin 2) (Fin 2) ℂ) :
    cuntzCornerMap S (Mᴴ) = star (cuntzCornerMap S M) := by
  dsimp [cuntzCornerMap, Matrix.conjTranspose_apply]
  simp only [star_add, star_smul, star_cuntzMatrixUnit, starRingEnd_apply]
  abel

theorem cuntzCornerMap_injective :
    Function.Injective (cuntzCornerMap S) := by
  intro M N h
  have h00 := congrArg (fun a => star (S 0) * a * S 0) h
  have h01 := congrArg (fun a => star (S 0) * a * S 1) h
  have h10 := congrArg (fun a => star (S 1) * a * S 0) h
  have h11 := congrArg (fun a => star (S 1) * a * S 1) h
  dsimp [cuntzCornerMap, cuntzMatrixUnit] at h00 h01 h10 h11
  simp only [mul_add, add_mul, smul_add, add_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_assoc,
    hC.isom₁, hC.isom₂, hC.ortho₁₂, hC.ortho₂₁, mul_one, mul_zero, smul_zero, zero_add, add_zero] at h00 h01 h10 h11
  ext i j
  have himp : ∀ x y : ℂ, x • (1 : A) = y • (1 : A) → x = y := by
    intro x y hxy
    have h1 : (x - y) • (1 : A) = 0 := by rw [sub_smul, hxy, sub_self]
    cases smul_eq_zero.mp h1 with
    | inl h2 => exact eq_of_sub_eq_zero h2
    | inr h2 => exact False.elim (one_ne_zero h2)
  fin_cases i <;> fin_cases j
  · exact himp _ _ h00
  · exact himp _ _ h01
  · exact himp _ _ h10
  · exact himp _ _ h11

/-- 3. Fibonacci Local Matrix and Cuntz Operator -/
def fibonacciMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![0, 1],
    ![1, 1]]

def fibonacciCuntzOperator : A :=
  S 0 * star (S 1) +
  S 1 * star (S 0) +
  S 1 * star (S 1)

theorem cuntzCornerMap_fibonacciMatrix :
    cuntzCornerMap S fibonacciMatrix = fibonacciCuntzOperator S := by
  dsimp [cuntzCornerMap, fibonacciMatrix, cuntzMatrixUnit, fibonacciCuntzOperator]
  simp only [zero_smul, one_smul, zero_add, add_zero]

/-- 4. Fusion Rules transported across the corner -/
theorem fibonacciMatrix_sq :
    fibonacciMatrix * fibonacciMatrix = fibonacciMatrix + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [fibonacciMatrix, Matrix.mul_apply]; try ring)

theorem fibonacciCuntzOperator_sq :
    fibonacciCuntzOperator S * fibonacciCuntzOperator S =
      fibonacciCuntzOperator S + 1 := by
  rw [← cuntzCornerMap_fibonacciMatrix S]
  rw [← cuntzCornerMap_mul S]
  rw [fibonacciMatrix_sq]
  rw [cuntzCornerMap_add, cuntzCornerMap_one S]

end CuntzMatrixCorner
