code = """import InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
import Mathlib.Tactic

namespace InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition

open Matrix

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Split Peirce Projectors for the hyperbolic J generator -/
def P_plus_J : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne + matJ)
def P_minus_J : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne - matJ)

/-- Split Peirce Projectors for the hyperbolic K generator -/
def P_plus_K : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne + matK)
def P_minus_K : Matrix (Fin 2) (Fin 2) R := ⅟(2 : R) • (matOne - matK)

theorem P_plus_J_add_P_minus_J : P_plus_J (R := R) + P_minus_J = matOne := by
  ext i j; fin_cases i <;> fin_cases j
  · dsimp [P_plus_J, P_minus_J, matOne, matJ]; have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * (1 + 1) + ⅟(2:R) * (1 - 1) = ⅟(2:R) * 2 := by ring
      _ = 1 := h2
  · dsimp [P_plus_J, P_minus_J, matOne, matJ]; ring
  · dsimp [P_plus_J, P_minus_J, matOne, matJ]; ring
  · dsimp [P_plus_J, P_minus_J, matOne, matJ]; have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * (1 + -1) + ⅟(2:R) * (1 - -1) = ⅟(2:R) * 2 := by ring
      _ = 1 := h2

theorem matJ_sq : matJ (R := R) * matJ = matOne := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [matJ, matOne, Matrix.mul_apply, dotProduct]; simp; ring)

theorem P_plus_J_sq : P_plus_J (R := R) * P_plus_J = P_plus_J := by
  ext i j; fin_cases i <;> fin_cases j
  · dsimp [P_plus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * 2 * (⅟(2:R) * 2) = 1 * 1 := by rw [h2]
      _ = 1 := by ring
      _ = ⅟(2:R) * 2 := by rw [h2]
  · dsimp [P_plus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring
  · dsimp [P_plus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring
  · dsimp [P_plus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring

theorem P_minus_J_sq : P_minus_J (R := R) * P_minus_J = P_minus_J := by
  ext i j; fin_cases i <;> fin_cases j
  · dsimp [P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring
  · dsimp [P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring
  · dsimp [P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring
  · dsimp [P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * 2 * (⅟(2:R) * 2) = 1 * 1 := by rw [h2]
      _ = 1 := by ring
      _ = ⅟(2:R) * 2 := by rw [h2]

theorem P_plus_J_mul_P_minus_J : P_plus_J (R := R) * P_minus_J = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring)

theorem P_minus_J_mul_P_plus_J : P_minus_J (R := R) * P_plus_J = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> (dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; ring)

/-- 
  The capstone reduction theorem: any chiral operator {D, J} = 0 is exactly projected 
  into the off-diagonal hyperbolic Dirac system.
-/
theorem chiral_off_diagonal_reduction (D : Matrix (Fin 2) (Fin 2) R)
    (h_chiral : D * matJ + matJ * D = 0) :
    D = P_plus_J * D * P_minus_J + P_minus_J * D * P_plus_J := by
  have ⟨h_d0, h_dj⟩ := chiral_anticommutation_reduction D h_chiral
  ext i j
  have h00 : D 0 0 = 0 := by
    have hd0 : ⅟(2:R) * (D 0 0 + D 1 1) = 0 := h_d0
    have hdj : ⅟(2:R) * (D 0 0 - D 1 1) = 0 := h_dj
    have sum : ⅟(2:R) * (D 0 0 + D 1 1) + ⅟(2:R) * (D 0 0 - D 1 1) = 0 := by rw [hd0, hdj, add_zero]
    have sum_eq : ⅟(2:R) * (D 0 0 + D 1 1) + ⅟(2:R) * (D 0 0 - D 1 1) = (⅟(2:R) * 2) * D 0 0 := by ring
    rw [sum_eq] at sum
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    rw [h2, one_mul] at sum; exact sum
  have h11 : D 1 1 = 0 := by
    have hd0 : ⅟(2:R) * (D 0 0 + D 1 1) = 0 := h_d0
    have hdj : ⅟(2:R) * (D 0 0 - D 1 1) = 0 := h_dj
    have sub : ⅟(2:R) * (D 0 0 + D 1 1) - ⅟(2:R) * (D 0 0 - D 1 1) = 0 := by rw [hd0, hdj, sub_zero]
    have sub_eq : ⅟(2:R) * (D 0 0 + D 1 1) - ⅟(2:R) * (D 0 0 - D 1 1) = (⅟(2:R) * 2) * D 1 1 := by ring
    rw [sub_eq] at sub
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    rw [h2, one_mul] at sub; exact sub
  fin_cases i <;> fin_cases j
  · dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; rw [h00]; ring
  · dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * (1 + 1) * D 0 1 * (⅟(2:R) * (1 + 1)) = (⅟(2:R) * 2) * (⅟(2:R) * 2) * D 0 1 := by ring
      _ = 1 * 1 * D 0 1 := by rw [h2]
      _ = D 0 1 := by ring
  · dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp
    have h2 : ⅟(2:R) * 2 = 1 := invOf_mul_self 2
    calc ⅟(2:R) * (1 + 1) * D 1 0 * (⅟(2:R) * (1 + 1)) = (⅟(2:R) * 2) * (⅟(2:R) * 2) * D 1 0 := by ring
      _ = 1 * 1 * D 1 0 := by rw [h2]
      _ = D 1 0 := by ring
  · dsimp [P_plus_J, P_minus_J, matOne, matJ, Matrix.mul_apply, dotProduct]; simp; rw [h11]; ring

end InfoGeometry.GrandUnification.CoquaternionicDiracDecomposition
"""

with open('/home/goutev/repos/info-geometry-lean/lean/sandbox/PeirceProjectors.lean', 'w') as f:
    f.write(code)
