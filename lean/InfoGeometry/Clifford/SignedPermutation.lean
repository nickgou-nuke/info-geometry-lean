import InfoGeometry.Clifford.Cl11Matrix
import Mathlib.LinearAlgebra.Matrix.Swap

open scoped Matrix

namespace SignedPermutation

open InfoGeometry.Clifford.Cl11Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The `Cl(1,1)` Pauli generators as concrete `2 × 2` real matrices. -/
abbrev e1 : Mat2 := Eplus

/-- The second `Cl(1,1)` Pauli generator as a real signed permutation matrix. -/
abbrev e2 : Mat2 := Eminus

/-- `e₁` is the identity permutation matrix with a sign diagonal. -/
theorem e1_eq_signedPermutation :
    e1 = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) * (1 : Mat2) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e1, Eplus, Matrix.diagonal]

/-- `e₂` is the swap permutation matrix with a sign diagonal. -/
theorem e2_eq_signedPermutation :
    e2 = Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1) *
      Matrix.swap ℝ 0 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e2, Eminus, Matrix.diagonal, Matrix.swap, Matrix.mul_apply, Fin.sum_univ_two]

/-- The first signed-permutation seed is symmetric. -/
theorem e1_transpose : e1ᵀ = e1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e1, Eplus, Matrix.transpose_apply]

/-- The second signed-permutation seed is skew-symmetric. -/
theorem e2_transpose : e2ᵀ = -e2 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [e2, Eminus, Matrix.transpose_apply]

/-- The first signed-permutation seed is orthogonal. -/
theorem e1_orthogonal : e1ᵀ * e1 = (1 : Mat2) := by
  rw [e1_transpose, e1]
  simpa using Eplus_sq

/-- The second signed-permutation seed is orthogonal. -/
theorem e2_orthogonal : e2ᵀ * e2 = (1 : Mat2) := by
  rw [e2_transpose]
  calc
    (-e2) * e2 = -(e2 * e2) := by
      simp [neg_mul]
    _ = - (-(1 : Mat2)) := by
      have hsq : e2 * e2 = -(1 : Mat2) := by
        simpa [e2] using Eminus_sq
      rw [hsq]
    _ = (1 : Mat2) := by
      simp

/-- The signed-permutation `Cl(1,1)` seed satisfies the split Clifford relations. -/
theorem signedPermutation_clifford_relations :
    e1 * e1 = 1 ∧ e2 * e2 = -(1 : Mat2) ∧ e1 * e2 + e2 * e1 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [e1] using Eplus_sq
  · simpa [e2] using Eminus_sq
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [e1, e2, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

end SignedPermutation
