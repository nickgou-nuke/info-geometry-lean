import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Split-Quaternions (Coquaternions) Matrix Representation

This file formalizes the $2 \times 2$ real matrix representation of the split-quaternion algebra $\mathbb{H}_{\text{split}}$.
The basis consists of $\{1, \mathbf{i}, \mathbf{j}, \mathbf{k}\}$ with the split signature $(-, +, +)$.
-/

namespace InfoGeometry.SplitQuaternion

open Matrix

/-- The standard identity matrix. -/
def splitOne : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- The imaginary unit `i`, corresponding to a rotation. `i^2 = -1`. -/
def splitI : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![-1, 0]]

/-- The hyperbolic unit `j`. `j^2 = +1`. -/
def splitJ : Matrix (Fin 2) (Fin 2) ℝ := ![![0, 1], ![1, 0]]

/-- The hyperbolic unit `k`. `k^2 = +1`. -/
def splitK : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, -1]]

/-! ### Squares (Diagonal Anticommutators) -/

@[simp] lemma splitI_sq : splitI * splitI = -splitOne := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitI, splitOne, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitJ_sq : splitJ * splitJ = splitOne := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitJ, splitOne, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitK_sq : splitK * splitK = splitOne := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitK, splitOne, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-! ### Commutators `[A, B] = AB - BA` -/

/-- `[i, j] = 2k` -/
lemma commutator_i_j : splitI * splitJ - splitJ * splitI = 2 • splitK := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitI, splitJ, splitK, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `[j, k] = -2i` -/
lemma commutator_j_k : splitJ * splitK - splitK * splitJ = -2 • splitI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitJ, splitK, splitI, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `[k, i] = 2j` -/
lemma commutator_k_i : splitK * splitI - splitI * splitK = 2 • splitJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitK, splitI, splitJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-! ### Cross-Anticommutators `{A, B} = AB + BA` -/

/-- `{i, j} = 0` -/
lemma anticommutator_i_j : splitI * splitJ + splitJ * splitI = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitI, splitJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `{j, k} = 0` -/
lemma anticommutator_j_k : splitJ * splitK + splitK * splitJ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitJ, splitK, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- `{k, i} = 0` -/
lemma anticommutator_k_i : splitK * splitI + splitI * splitK = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitK, splitI, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-! ### Derived Product Laws -/

@[simp] lemma splitI_mul_splitJ : splitI * splitJ = splitK := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitI, splitJ, splitK, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitJ_mul_splitI : splitJ * splitI = -splitK := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitJ, splitI, splitK, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitJ_mul_splitK : splitJ * splitK = -splitI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitJ, splitK, splitI, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitK_mul_splitJ : splitK * splitJ = splitI := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitK, splitJ, splitI, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitK_mul_splitI : splitK * splitI = splitJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitK, splitI, splitJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

@[simp] lemma splitI_mul_splitK : splitI * splitK = -splitJ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [splitI, splitK, splitJ, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

end InfoGeometry.SplitQuaternion
