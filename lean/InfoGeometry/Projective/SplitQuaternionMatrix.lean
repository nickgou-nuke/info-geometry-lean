import Mathlib.Algebra.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitQuaternionMatrix

This file establishes the foundational isomorphism between the split-quaternions
($\mathbb{H}_s$) and the algebra of $2 \times 2$ real matrices ($M_2(\mathbb{R})$).

This continuous frame handles the continuous transformations of the Lorentz group
$SL(2, \mathbb{R}) \times SL(2, \mathbb{R})$ acting on the null coordinates in Twistor Geometry.

The basis $\{1, i, j, k\}$ is taken from $M_2(\mathbb{R})$ corresponding to the dihedral group of a square.
-/

namespace InfoGeometry.Projective

open Matrix

/-- The canonical basis element 1 (Identity) in $M_2(\mathbb{R})$ -/
def mat_1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, 1]

/-- The canonical basis element i in $M_2(\mathbb{R})$ -/
def mat_i : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; -1, 0]

/-- The canonical basis element j in $M_2(\mathbb{R})$ -/
def mat_j : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

/-- The canonical basis element k in $M_2(\mathbb{R})$ -/
def mat_k : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-! ### Structural properties of the basis -/

theorem mat_j_sq : mat_j * mat_j = mat_1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_j, mat_1, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_k_sq : mat_k * mat_k = mat_1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_k, mat_1, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_i_sq : mat_i * mat_i = -mat_1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_i, mat_1, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_j_mul_k : mat_j * mat_k = -mat_i := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_j, mat_k, mat_i, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_k_mul_j : mat_k * mat_j = mat_i := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_k, mat_j, mat_i, Matrix.mul_apply, Fin.sum_univ_two]

/-- Split-quaternion `j,k` anticommutation in the matrix model. -/
theorem mat_jk_anticomm : mat_j * mat_k + mat_k * mat_j = 0 := by
  rw [mat_j_mul_k, mat_k_mul_j]
  abel

theorem mat_i_mul_j : mat_i * mat_j = mat_k := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_i, mat_j, mat_k, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_j_mul_i : mat_j * mat_i = -mat_k := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_i, mat_j, mat_k, Matrix.mul_apply, Fin.sum_univ_two]

/-- Split-quaternion `i,j` anticommutation in the matrix model. -/
theorem mat_ij_anticomm : mat_i * mat_j + mat_j * mat_i = 0 := by
  rw [mat_i_mul_j, mat_j_mul_i]
  abel

theorem mat_k_mul_i : mat_k * mat_i = mat_j := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_k, mat_i, mat_j, Matrix.mul_apply, Fin.sum_univ_two]

theorem mat_i_mul_k : mat_i * mat_k = -mat_j := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [mat_k, mat_i, mat_j, Matrix.mul_apply, Fin.sum_univ_two]

/-- Split-quaternion `k,i` anticommutation in the matrix model. -/
theorem mat_ki_anticomm : mat_k * mat_i + mat_i * mat_k = 0 := by
  rw [mat_k_mul_i, mat_i_mul_k]
  abel

theorem det_mat_1 : mat_1.det = 1 := by
  norm_num [mat_1, Matrix.det_fin_two]

theorem det_mat_i : mat_i.det = 1 := by
  norm_num [mat_i, Matrix.det_fin_two]

theorem det_mat_j : mat_j.det = -1 := by
  norm_num [mat_j, Matrix.det_fin_two]

theorem det_mat_k : mat_k.det = -1 := by
  norm_num [mat_k, Matrix.det_fin_two]

/-- The quadratic norm representation for the division-binarion representation.
    $N(q) = w^2 + x^2 - y^2 - z^2$, which corresponds to the matrix determinant. -/
def splitNormSq (w x y z : ℝ) : ℝ :=
  w^2 + x^2 - y^2 - z^2

/--
The explicit matrix mapping from split quaternion coordinates to $M_2(\mathbb{R})$.
$q = w + x i + y j + z k$.
-/
def splitQuaternionToMatrix (w x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  w • mat_1 + x • mat_i + y • mat_j + z • mat_k

theorem det_splitQuaternionToMatrix (w x y z : ℝ) :
    (splitQuaternionToMatrix w x y z).det = splitNormSq w x y z := by
  unfold splitQuaternionToMatrix splitNormSq mat_1 mat_i mat_j mat_k
  norm_num [Matrix.det_fin_two]
  ring

/-- Determinant of the matrix model agrees with the split norm on coordinates. -/
theorem det_eq_splitNormSq (w x y z : ℝ) :
    (splitQuaternionToMatrix w x y z).det = splitNormSq w x y z :=
  det_splitQuaternionToMatrix w x y z

/-- Explicit trace on `2 × 2` matrices. -/
def tr2 (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 0 0 + M 1 1

theorem tr2_mat_1 : tr2 mat_1 = 2 := by
  norm_num [tr2, mat_1]

theorem tr2_mat_i : tr2 mat_i = 0 := by
  norm_num [tr2, mat_i]

theorem tr2_mat_j : tr2 mat_j = 0 := by
  norm_num [tr2, mat_j]

theorem tr2_mat_k : tr2 mat_k = 0 := by
  norm_num [tr2, mat_k]

/-- Basis orthogonality readout under the trace pairing `Tr(AB)`. -/
theorem tr2_mat_i_mul_j : tr2 (mat_i * mat_j) = 0 := by
  rw [mat_i_mul_j]
  exact tr2_mat_k

theorem tr2_mat_j_mul_k : tr2 (mat_j * mat_k) = 0 := by
  rw [mat_j_mul_k]
  norm_num [tr2, mat_i]

/--
The split-quaternion algebra $\mathbb{H}_s$ over $\mathbb{R}$.
-/
structure SplitQuaternion where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/--
Concrete matrix realization of a split quaternion.
-/
def splitQuaternionToMatrixQ (q : SplitQuaternion) : Matrix (Fin 2) (Fin 2) ℝ :=
  splitQuaternionToMatrix q.w q.x q.y q.z

/--
Inverse coordinate readback from `M₂(ℝ)` to split-quaternion coordinates.
-/
noncomputable def matrixToSplitQuaternion (M : Matrix (Fin 2) (Fin 2) ℝ) : SplitQuaternion where
  w := (M 0 0 + M 1 1) / 2
  x := (M 0 1 - M 1 0) / 2
  y := (M 0 1 + M 1 0) / 2
  z := (M 0 0 - M 1 1) / 2

theorem splitQuaternionToMatrixQ_matrixToSplitQuaternion
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    splitQuaternionToMatrixQ (matrixToSplitQuaternion M) = M := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [splitQuaternionToMatrixQ, matrixToSplitQuaternion,
      splitQuaternionToMatrix, mat_1, mat_i, mat_j, mat_k]
    <;> ring

theorem matrixToSplitQuaternion_splitQuaternionToMatrixQ
    (q : SplitQuaternion) :
    matrixToSplitQuaternion (splitQuaternionToMatrixQ q) = q := by
  cases q
  simp [matrixToSplitQuaternion, splitQuaternionToMatrixQ,
    splitQuaternionToMatrix, mat_1, mat_i, mat_j, mat_k]
  constructor <;> ring

/--
Equivalence between split-quaternion coordinates and `M₂(ℝ)`.
-/
noncomputable def splitQuaternionEquivMatrix :
    SplitQuaternion ≃ Matrix (Fin 2) (Fin 2) ℝ where
  toFun := splitQuaternionToMatrixQ
  invFun := matrixToSplitQuaternion
  left_inv := matrixToSplitQuaternion_splitQuaternionToMatrixQ
  right_inv := splitQuaternionToMatrixQ_matrixToSplitQuaternion

noncomputable instance : AddCommGroup SplitQuaternion :=
  Equiv.addCommGroup splitQuaternionEquivMatrix

noncomputable instance : Module ℝ SplitQuaternion :=
  Equiv.module ℝ splitQuaternionEquivMatrix

noncomputable instance : Ring SplitQuaternion :=
  Equiv.ring splitQuaternionEquivMatrix

noncomputable instance : Algebra ℝ SplitQuaternion :=
  Equiv.algebra ℝ splitQuaternionEquivMatrix

/--
The fundamental equivalence $\mathbb{H}_s \cong M_2(\mathbb{R})$.
With the exact mapping provided, this equivalence is structurally fixed.

-/
noncomputable def splitQuaternionMatrixEquiv :
    SplitQuaternion ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  { toFun := splitQuaternionToMatrixQ
    invFun := matrixToSplitQuaternion
    left_inv := matrixToSplitQuaternion_splitQuaternionToMatrixQ
    right_inv := splitQuaternionToMatrixQ_matrixToSplitQuaternion
    map_mul' := by
      intro a b
      change
        splitQuaternionEquivMatrix
            (splitQuaternionEquivMatrix.symm
              (splitQuaternionEquivMatrix a * splitQuaternionEquivMatrix b))
          =
        splitQuaternionEquivMatrix a * splitQuaternionEquivMatrix b
      simp
    map_add' := by
      intro a b
      change
        splitQuaternionEquivMatrix
            (splitQuaternionEquivMatrix.symm
              (splitQuaternionEquivMatrix a + splitQuaternionEquivMatrix b))
          =
        splitQuaternionEquivMatrix a + splitQuaternionEquivMatrix b
      simp
    commutes' := by
      intro r
      change
        splitQuaternionEquivMatrix
            (splitQuaternionEquivMatrix.symm
              (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) r))
          =
        algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) r
      simp }

end InfoGeometry.Projective
