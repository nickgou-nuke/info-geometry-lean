import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.LieOrbitSymmetryChart2x2

Concrete symmetry-adapted chart seed in `2×2`:
for a diagonal generator with distinct eigenvalues, commuting matrices are diagonal.

No wrappers. No `sorry`.
-/

namespace InfoGeometry.Canonical.LieOrbitSymmetryChart2x2

open Matrix

abbrev M2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

section

variable {R : Type*} [Field R]

/-- Diagonal seed with eigenvalues `a,b`. -/
def diag₂ (a b : R) : M2 R :=
  !![a, 0;
     0, b]

theorem commute_diag₂_offdiag_zero
    (a b : R) (hab : a ≠ b) (X : M2 R)
    (hcomm : X * diag₂ a b = diag₂ a b * X) :
    X 0 1 = 0 ∧ X 1 0 = 0 := by
  have h01 : (X * diag₂ a b) 0 1 = (diag₂ a b * X) 0 1 := by
    simpa using congrArg (fun M => M 0 1) hcomm
  have h10 : (X * diag₂ a b) 1 0 = (diag₂ a b * X) 1 0 := by
    simpa using congrArg (fun M => M 1 0) hcomm
  have h01' : X 0 1 * b = a * X 0 1 := by
    simpa [diag₂, Matrix.mul_apply, Fin.sum_univ_two] using h01
  have h10' : X 1 0 * a = b * X 1 0 := by
    simpa [diag₂, Matrix.mul_apply, Fin.sum_univ_two] using h10
  have hab' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hmul01 : (b - a) * X 0 1 = 0 := by
    calc
      (b - a) * X 0 1 = b * X 0 1 - a * X 0 1 := by ring
      _ = X 0 1 * b - a * X 0 1 := by ring
      _ = 0 := by simpa using sub_eq_zero.mpr h01'
  have hX01 : X 0 1 = 0 := by
    rcases mul_eq_zero.mp hmul01 with hba0 | hX01
    · exact (hab' hba0).elim
    · exact hX01
  have hmul10 : (a - b) * X 1 0 = 0 := by
    calc
      (a - b) * X 1 0 = a * X 1 0 - b * X 1 0 := by ring
      _ = X 1 0 * a - b * X 1 0 := by ring
      _ = 0 := by simpa using sub_eq_zero.mpr h10'
  have hab'' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hX10 : X 1 0 = 0 := by
    rcases mul_eq_zero.mp hmul10 with hab0 | hX10
    · exact (hab'' hab0).elim
    · exact hX10
  exact ⟨hX01, hX10⟩

theorem commute_diag₂_iff_diagonal
    (a b : R) (hab : a ≠ b) (X : M2 R) :
    X * diag₂ a b = diag₂ a b * X ↔ ∃ u v : R, X = !![u, 0; 0, v] := by
  constructor
  · intro hcomm
    rcases commute_diag₂_offdiag_zero a b hab X hcomm with ⟨h01, h10⟩
    refine ⟨X 0 0, X 1 1, ?_⟩
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [h01, h10]
  · rintro ⟨u, v, rfl⟩
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [diag₂, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end

end InfoGeometry.Canonical.LieOrbitSymmetryChart2x2
