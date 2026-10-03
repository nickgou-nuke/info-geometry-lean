import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import Mathlib.Tactic

namespace InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition

open Matrix

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

lemma matOne_mul (M : Matrix (Fin 2) (Fin 2) R) : matOne * M = M := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, Matrix.mul_apply, dotProduct]; ring)

lemma mul_matOne (M : Matrix (Fin 2) (Fin 2) R) : M * matOne = M := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, Matrix.mul_apply, dotProduct]; ring)

/-- Split Peirce Projectors for the hyperbolic J generator -/
def P_plus_J : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne + matJ)
def P_minus_J : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne - matJ)

/-- Split Peirce Projectors for the hyperbolic K generator -/
def P_plus_K : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne + matK)
def P_minus_K : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne - matK)

theorem P_plus_J_add_P_minus_J : P_plus_J (R := R) + P_minus_J = matOne := by
  dsimp [P_plus_J, P_minus_J]
  rw [← smul_add]
  have h_add : matOne (R := R) + matJ + (matOne - matJ) = (2:R) • matOne := by
    ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, matJ]; ring)
  rw [h_add, smul_smul]
  have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
  rw [h2, one_smul]

theorem matJ_sq : matJ (R := R) * matJ = matOne := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matJ, matOne, Matrix.mul_apply, dotProduct]; ring)

theorem P_plus_J_sq : P_plus_J (R := R) * P_plus_J = P_plus_J := by
  dsimp [P_plus_J]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_mul : (matOne (R := R) + matJ) * (matOne + matJ) = (2:R) • (matOne + matJ) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw [matOne_mul, mul_matOne, mul_matOne, matJ_sq]
    have h_sum : matOne (R:=R) + matJ + (matJ + matOne) = (2:R) • (matOne + matJ) := by
      ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, matJ]; ring)
    exact h_sum
  rw [h_mul, smul_smul]
  have h_coeff : ⅟(2:R) * (⅟(2:R) * 2) = ⅟(2:R) := by
    rw [invOf_mul_self 2, mul_one]
  have h_assoc : ⅟(2:R) * ⅟(2:R) * 2 = ⅟(2:R) * (⅟(2:R) * 2) := by ring
  rw [h_assoc, h_coeff]

theorem P_minus_J_sq : P_minus_J (R := R) * P_minus_J = P_minus_J := by
  dsimp [P_minus_J]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_mul : (matOne (R := R) - matJ) * (matOne - matJ) = (2:R) • (matOne - matJ) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    rw [matOne_mul, mul_matOne, mul_matOne, matJ_sq]
    have h_sum : matOne (R:=R) - matJ - (matJ - matOne) = (2:R) • (matOne - matJ) := by
      ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, matJ]; ring)
    exact h_sum
  rw [h_mul, smul_smul]
  have h_coeff : ⅟(2:R) * (⅟(2:R) * 2) = ⅟(2:R) := by
    rw [invOf_mul_self 2, mul_one]
  have h_assoc : ⅟(2:R) * ⅟(2:R) * 2 = ⅟(2:R) * (⅟(2:R) * 2) := by ring
  rw [h_assoc, h_coeff]

theorem P_plus_J_mul_P_minus_J : P_plus_J (R := R) * P_minus_J = 0 := by
  dsimp [P_plus_J, P_minus_J]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_mul : (matOne (R := R) + matJ) * (matOne - matJ) = 0 := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    rw [matOne_mul, mul_matOne, mul_matOne, matJ_sq]
    have h_sum : matOne (R:=R) - matJ + (matJ - matOne) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, matJ]; ring)
    exact h_sum
  rw [h_mul, smul_zero]

theorem P_minus_J_mul_P_plus_J : P_minus_J (R := R) * P_plus_J = 0 := by
  dsimp [P_plus_J, P_minus_J]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h_mul : (matOne (R := R) - matJ) * (matOne + matJ) = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    rw [matOne_mul, mul_matOne, mul_matOne, matJ_sq]
    have h_sum : matOne (R:=R) + matJ - (matJ + matOne) = 0 := by
      ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matOne, matJ]; ring)
    exact h_sum
  rw [h_mul, smul_zero]

/-- 
  The capstone reduction theorem: any chiral operator {D, J} = 0 is exactly projected 
  into the off-diagonal hyperbolic Dirac system.
-/
theorem chiral_off_diagonal_reduction (D : Matrix (Fin 2) (Fin 2) R)
    (h_chiral : D * matJ + matJ * D = 0) :
    D = P_plus_J * D * P_minus_J + P_minus_J * D * P_plus_J := by
  have h_dj : D * matJ = - matJ * D := by
    calc D * matJ = D * matJ + matJ * D - matJ * D := by
          ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.add_apply, Matrix.sub_apply]; ring)
      _ = 0 - matJ * D := by rw [h_chiral]
      _ = - matJ * D := by
          ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.zero_apply, Matrix.sub_apply, Matrix.neg_apply]; ring)
  
  dsimp [P_plus_J, P_minus_J]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul]
  rw [smul_smul, smul_smul, ← smul_add]
  
  have h_inner_plus : (matOne + matJ) * D * (matOne - matJ) = D - matJ * D * matJ + matJ * D - D * matJ := by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub]
    rw [matOne_mul, mul_matOne, matOne_mul]
    ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.add_apply, Matrix.sub_apply]; ring)
  
  have h_inner_minus : (matOne - matJ) * D * (matOne + matJ) = D - matJ * D * matJ - matJ * D + D * matJ := by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add]
    rw [matOne_mul, mul_matOne, matOne_mul]
    ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.add_apply, Matrix.sub_apply]; ring)
  
  rw [h_inner_plus, h_inner_minus]
  
  have h_sum : D - matJ * D * matJ + matJ * D - D * matJ + (D - matJ * D * matJ - matJ * D + D * matJ) = (2:R) • (D - matJ * D * matJ) := by
    ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.add_apply, Matrix.sub_apply]; ring)
  rw [h_sum, smul_smul]
  
  have h_j_comm : matJ * D * matJ = - D := by
    calc matJ * D * matJ = matJ * (D * matJ) := by
          ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.mul_apply]; ring)
      _ = matJ * (- matJ * D) := by rw [h_dj]
      _ = - (matJ * matJ) * D := by
          ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.mul_apply, matJ, Matrix.neg_apply]; ring)
      _ = - matOne * D := by rw [matJ_sq]
      _ = - D := by
          rw [matOne_mul]
          ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.mul_apply, Matrix.neg_apply, matOne]; ring)
  
  have h_diff : D - matJ * D * matJ = (2:R) • D := by
    rw [h_j_comm]
    ext i j; fin_cases i <;> fin_cases j <;> (dsimp [Matrix.sub_apply, Matrix.neg_apply]; ring)
  rw [h_diff, smul_smul]
  
  have h_coeff : ⅟(2:R) * ⅟(2:R) * 2 * 2 = 1 := by
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * ⅟(2:R) * 2 * 2 = (⅟(2:R) * 2) * (⅟(2:R) * 2) := by ring
      _ = 1 * 1 := by rw [h2]
      _ = 1 := by ring
  
  rw [h_coeff, one_smul]

end InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
