import Mathlib
import InfoGeometryCore.Basic

/-!

# InfoGeometry.Algebra.SplitQuaternionMatrices

#### BUCKET 1: CLOSED FINITE THEOREMS

[split-quaternion matrix multiplication table, split idempotents, nilpotent
element, coordinate determinant/norm formula, determinant multiplicativity,
trace/readout formula.]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

[None.]

#### BUCKET 3: OPEN CLOSURE DEBT

[No split-octonion Bektaş operator-correctness theorem. No Albert/Freudenthal
determinant theorem. No ordinary associative algebra equivalence is stated
beyond the finite split-quaternion `M₂(ℝ)` coordinate model.]

Source audit: 
-/

namespace SplitQuaternionMatrices

open Matrix

open InfoGeometryCore

/-- Split-quaternion elliptic unit: `i² = -1`. -/
def sqI : M2R :=
!![0, 1;
-1, 0]

/-- Split-quaternion hyperbolic unit: `j² = 1`. -/
def sqJ : M2R :=
!![0, 1;
1, 0]

/-- Split-quaternion hyperbolic unit: `k² = 1`. -/
def sqK : M2R :=
!![1, 0;
0, -1]

@[simp]
theorem sqI_sq :
sqI * sqI = -(1 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqJ_sq :
sqJ * sqJ = (1 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqK_sq :
sqK * sqK = (1 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqI_mul_sqJ :
sqI * sqJ = sqK := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqJ_mul_sqI :
sqJ * sqI = -sqK := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqJ_mul_sqK :
sqJ * sqK = -sqI := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqK_mul_sqJ :
sqK * sqJ = sqI := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqK_mul_sqI :
sqK * sqI = sqJ := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem sqI_mul_sqK :
sqI * sqK = -sqJ := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

/-- Positive split idempotent `(1+j)/2`. -/
noncomputable def Pplus : M2R :=
(1 / 2 : ℝ) • ((1 : M2R) + sqJ)

/-- Negative split idempotent `(1-j)/2`. -/
noncomputable def Pminus : M2R :=
(1 / 2 : ℝ) • ((1 : M2R) - sqJ)

@[simp]
theorem Pplus_idempotent :
Pplus * Pplus = Pplus := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Pplus, sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_idempotent :
Pminus * Pminus = Pminus := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Pminus, sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_mul_Pminus :
Pplus * Pminus = (0 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Pplus, Pminus, sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pminus_mul_Pplus :
Pminus * Pplus = (0 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Pplus, Pminus, sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Pplus_add_Pminus :
Pplus + Pminus = (1 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Pplus, Pminus, sqJ]

/-- Nilpotent split-quaternion element `i-j`. -/
def Nsplit : M2R :=
sqI - sqJ

@[simp]
theorem Nsplit_sq_zero :
Nsplit * Nsplit = (0 : M2R) := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
norm_num [Nsplit, sqI, sqJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem Nsplit_ne_zero :
Nsplit ≠ (0 : M2R) := by
intro h
have h10 := congrArg (fun A : M2R => A 1 0) h
norm_num [Nsplit, sqI, sqJ] at h10

/--
Coordinate realization of a split quaternion

`w + x i + y j + z k`

as a real `2×2` matrix.
-/
def splitQ (w x y z : ℝ) : M2R :=
w • (1 : M2R) + x • sqI + y • sqJ + z • sqK

/-- Explicit matrix entries of the split-quaternion coordinate map. -/
theorem splitQ_eq_matrix (w x y z : ℝ) :
splitQ w x y z =
!![w + z, x + y;
y - x, w - z] := by
ext i j
all_goals fin_cases i <;> fin_cases j <;>
simp [splitQ, sqI, sqJ, sqK] <;> ring

/-- Coordinate determinant for `2×2` real matrices. -/
def det2 (A : M2R) : ℝ :=
A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Coordinate trace for `2×2` real matrices. -/
def trace2 (A : M2R) : ℝ :=
A 0 0 + A 1 1

/--
The split-quaternion determinant/norm has signature `(2,2)`:

`N(w + xi + yj + zk) = w² + x² - y² - z²`.
-/
theorem det2_splitQ (w x y z : ℝ) :
det2 (splitQ w x y z) =
w * w + x * x - y * y - z * z := by
rw [splitQ_eq_matrix]
unfold det2
norm_num
ring

/-- The real-part readout is half the trace; equivalently `trace = 2w`. -/
theorem trace2_splitQ (w x y z : ℝ) :
trace2 (splitQ w x y z) = 2 * w := by
rw [splitQ_eq_matrix]
unfold trace2
norm_num
ring

/-- The coordinate determinant is multiplicative on `M₂(ℝ)`. -/
theorem det2_mul (A B : M2R) :
det2 (A * B) = det2 A * det2 B := by
unfold det2
simp [Matrix.mul_apply, Fin.sum_univ_two]
ring

/-- Multiplicativity of the split-quaternion norm through the matrix model. -/
theorem det2_splitQ_mul
(w x y z a b c d : ℝ) :
det2 (splitQ w x y z * splitQ a b c d) =
det2 (splitQ w x y z) * det2 (splitQ a b c d) := by
exact det2_mul (splitQ w x y z) (splitQ a b c d)

/-- A nonzero square-zero split-quaternion matrix is not the zero matrix. -/
theorem nonzero_nilpotent_split_quaternion :
Nsplit * Nsplit = (0 : M2R) ∧ Nsplit ≠ (0 : M2R) :=
⟨Nsplit_sq_zero, Nsplit_ne_zero⟩

/--
The two split idempotents are complementary orthogonal projectors.
-/
theorem split_idempotent_projector_packet :
Pplus * Pplus = Pplus ∧
Pminus * Pminus = Pminus ∧
Pplus * Pminus = 0 ∧
Pminus * Pplus = 0 ∧
Pplus + Pminus = (1 : M2R) :=
⟨Pplus_idempotent,
Pminus_idempotent,
Pplus_mul_Pminus,
Pminus_mul_Pplus,
Pplus_add_Pminus⟩

/--
The split-quaternion matrix basis satisfies the defining multiplication table.
-/
theorem split_quaternion_basis_packet :
sqI * sqI = -(1 : M2R) ∧
sqJ * sqJ = (1 : M2R) ∧
sqK * sqK = (1 : M2R) ∧
sqI * sqJ = sqK ∧
sqJ * sqI = -sqK ∧
sqJ * sqK = -sqI ∧
sqK * sqJ = sqI ∧
sqK * sqI = sqJ ∧
sqI * sqK = -sqJ :=
⟨sqI_sq,
sqJ_sq,
sqK_sq,
sqI_mul_sqJ,
sqJ_mul_sqI,
sqJ_mul_sqK,
sqK_mul_sqJ,
sqK_mul_sqI,
sqI_mul_sqK⟩

end SplitQuaternionMatrices
