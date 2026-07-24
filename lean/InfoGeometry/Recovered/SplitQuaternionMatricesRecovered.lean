import Mathlib

/-!
# Split-quaternion 2×2 real matrix core

This recovered module now contains only kernel-checked matrix facts.  Former
Clifford/CAR/amplituhedron claims that depended on unproved bridge lemmas are
not installed here.
-/

namespace InfoGeometry.SplitQuaternion

open Matrix

/-- The identity matrix. -/
def splitOne : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Generator squaring to `-1`. -/
def splitI : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![-1, 0]]

/-- Generator squaring to `1`. -/
def splitJ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]

/-- Diagonal generator squaring to `1`. -/
def splitK : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]

@[simp] lemma splitI_sq : splitI * splitI = -splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitI, splitOne, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitJ_sq : splitJ * splitJ = splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitJ, splitOne, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitK_sq : splitK * splitK = splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitK, splitOne, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitI_mul_splitJ : splitI * splitJ = splitK := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitI, splitJ, splitK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitJ_mul_splitI : splitJ * splitI = -splitK := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitJ, splitI, splitK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitJ_mul_splitK : splitJ * splitK = -splitI := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitJ, splitK, splitI, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitK_mul_splitJ : splitK * splitJ = splitI := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitK, splitJ, splitI, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitK_mul_splitI : splitK * splitI = splitJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitK, splitI, splitJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma splitI_mul_splitK : splitI * splitK = -splitJ := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitI, splitK, splitJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- Split-quaternion conjugation/adjugate for a 2×2 matrix. -/
def splitConj (M : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![M 1 1, -M 0 1], ![-M 1 0, M 0 0]]

/-- Determinant/norm of a 2×2 matrix. -/
def splitNorm (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

lemma mul_splitConj (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M * splitConj M = (splitNorm M) • splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitConj, splitNorm, splitOne, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

lemma splitConj_mul (M : Matrix (Fin 2) (Fin 2) ℝ) :
    splitConj M * M = (splitNorm M) • splitOne := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [splitConj, splitNorm, splitOne, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

lemma split_inverse_theorem (M : Matrix (Fin 2) (Fin 2) ℝ) (h : splitNorm M ≠ 0) :
    M * ((splitNorm M)⁻¹ • splitConj M) = splitOne := by
  rw [Matrix.mul_smul, mul_splitConj, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- Spacetime coordinate embedding in the split-quaternion basis. -/
noncomputable def spacetimeMatrix (t x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  t • splitOne + x • splitI + y • splitJ + z • splitK

/-- Determinant of the split-quaternion spacetime matrix. -/
lemma det_spacetimeMatrix (t x y z : ℝ) :
    (spacetimeMatrix t x y z).det = t ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  simp [spacetimeMatrix, splitOne, splitI, splitJ, splitK, Matrix.det_fin_two]
  ring

end InfoGeometry.SplitQuaternion
