import Mathlib

open scoped Matrix

namespace InfoGeometry.Canonical

/-!
# A concrete split-Clifford matrix calculation

This file records only the explicit identities of four real `2 x 2` matrices.
The existing `InfoGeometry.Clifford.Cl11Quaternion` module owns the algebra
equivalence between `Cl(1,1)` and `M₂(ℝ)`; these lemmas do not re-prove that
equivalence or assert a relation to the split octonions.
-/

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℝ

def I₂ : Mat₂ := !![(1 : ℝ), 0; 0, 1]

def L₂ : Mat₂ := !![(1 : ℝ), 0; 0, -1]

def Icomp : Mat₂ := !![(0 : ℝ), -1; 1, 0]

def Lcomp : Mat₂ := !![(0 : ℝ), -1; -1, 0]

theorem Icomp_sq : Icomp * Icomp = -I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Icomp, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem Lcomp_sq : Lcomp * Lcomp = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lcomp, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem L₂_sq : L₂ * L₂ = I₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L₂, I₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem Icomp_mul_Lcomp : Icomp * Lcomp = L₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Icomp, Lcomp, L₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem Lcomp_mul_Icomp : Lcomp * Icomp = -L₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Icomp, Lcomp, L₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem Icomp_Lcomp_anticomm :
    Icomp * Lcomp + Lcomp * Icomp = 0 := by
  rw [Icomp_mul_Lcomp, Lcomp_mul_Icomp]
  simp

theorem Icomp_Lcomp_commutator :
    Icomp * Lcomp - Lcomp * Icomp = (2 : ℝ) • L₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Icomp, Lcomp, L₂, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem chiral_clifford_matrix_relations :
    (Icomp * Icomp = -I₂) ∧
    (Lcomp * Lcomp = I₂) ∧
    (Icomp * Lcomp = L₂) ∧
    (Lcomp * Icomp = -L₂) ∧
    (Icomp * Lcomp - Lcomp * Icomp = (2 : ℝ) • L₂) :=
  ⟨Icomp_sq, Lcomp_sq, Icomp_mul_Lcomp, Lcomp_mul_Icomp,
    Icomp_Lcomp_commutator⟩

end InfoGeometry.Canonical
