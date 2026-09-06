import Mathlib.Tactic

/-!
# Kasparov--Krein BdG doubling

Repaired external file: a concrete `2×2` BdG matrix has zero trace; its off-
diagonal chiral sector anticommutes with `σ_z` exactly.
-/

noncomputable section

namespace KasparovKrein

open Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- BdG matrix with diagonal mass `h` and pairing `Δ`. -/
def BdG_Matrix (h Δ : ℂ) : Mat2 := !![h, Δ; Δ, -h]

/-- Off-diagonal/chiral BdG matrix. -/
def BdG_OffDiag (Δ : ℂ) : Mat2 := BdG_Matrix 0 Δ

/-- Chiral grading `σ_z`. -/
def sigma_z : Mat2 := !![1, 0; 0, -1]

/-- Exact chiral anticommutation for the off-diagonal BdG sector. -/
theorem krein_chiral_symmetry (Δ : ℂ) :
    BdG_OffDiag Δ * sigma_z + sigma_z * BdG_OffDiag Δ = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [BdG_OffDiag, BdG_Matrix, sigma_z, Matrix.mul_apply, Fin.sum_univ_two]

/-- The full `2×2` BdG matrix is traceless. -/
theorem bdg_trace_zero (h Δ : ℂ) : Matrix.trace (BdG_Matrix h Δ) = 0 := by
  simp [BdG_Matrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- Its determinant is the quadratic `-h²-Δ²`. -/
theorem bdg_det (h Δ : ℂ) : (BdG_Matrix h Δ).det = -(h ^ 2 + Δ ^ 2) := by
  simp [BdG_Matrix, Matrix.det_fin_two]
  ring

#check krein_chiral_symmetry
#check bdg_trace_zero
#check bdg_det

end KasparovKrein
