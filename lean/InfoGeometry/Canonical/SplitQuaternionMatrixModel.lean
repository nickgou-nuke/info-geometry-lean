import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Clifford.SplitQ11CausalCone
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit split-complex and split-quaternion matrix model

This file records the finite real `2 × 2` matrix model used by the local
Tomita-Krein / split-quaternion atom.

It proves the concrete determinant formulas:

* split-complex coordinates `a + b ε` have determinant `a² - b²`;
* split-quaternion coordinates
  `w·1 + x·I + y·J + z·K` have determinant `w² + x² - y² - z²`.

It also proves the canonical idempotents, nilpotents, and zero-divisor products.
No infinite current algebra, twistor theorem, or octonion multiplication table is
introduced here.
-/

open scoped Matrix

namespace InfoGeometry.Canonical.SplitQuaternionMatrixModel

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.SplitQ11CausalCone

noncomputable section

abbrev Mat2 : Type :=
  Matrix (Fin 2) (Fin 2) ℝ

/-- Split-complex generator `ε² = 1`, represented by `diag(1,-1)`. -/
def splitComplexEpsilon : Mat2 :=
  Eplus

/-- Square-minus split-quaternion unit. -/
def splitQuaternionI : Mat2 :=
  Eminus

/-- First square-plus split-quaternion unit. -/
def splitQuaternionJ : Mat2 :=
  J1

/-- Second square-plus split-quaternion unit. -/
def splitQuaternionK : Mat2 :=
  Eplus

/-- Split-complex coordinate matrix `a + b ε`. -/
def splitComplexMatrix (a b : ℝ) : Mat2 :=
  a • (1 : Mat2) + b • splitComplexEpsilon

/-- Split-quaternion coordinate matrix `w·1 + x·I + y·J + z·K`. -/
def splitQuaternionMatrix (w x y z : ℝ) : Mat2 :=
  w • (1 : Mat2) + x • splitQuaternionI + y • splitQuaternionJ + z • splitQuaternionK

@[simp] theorem splitComplexEpsilon_sq :
    splitComplexEpsilon * splitComplexEpsilon = (1 : Mat2) := by
  simpa [splitComplexEpsilon] using Eplus_sq

@[simp] theorem splitQuaternionI_sq :
    splitQuaternionI * splitQuaternionI = -(1 : Mat2) := by
  simpa [splitQuaternionI] using Eminus_sq

@[simp] theorem splitQuaternionJ_sq :
    splitQuaternionJ * splitQuaternionJ = (1 : Mat2) := by
  simpa [splitQuaternionJ] using J1_sq

@[simp] theorem splitQuaternionK_sq :
    splitQuaternionK * splitQuaternionK = (1 : Mat2) := by
  simpa [splitQuaternionK] using Eplus_sq

theorem splitQuaternionI_mul_splitQuaternionJ :
    splitQuaternionI * splitQuaternionJ = splitQuaternionK := by
  simpa [splitQuaternionI, splitQuaternionJ, splitQuaternionK]
    using (matrix_split_quaternion_basis_laws).2.2.2.1

theorem splitQuaternionJ_mul_splitQuaternionI :
    splitQuaternionJ * splitQuaternionI = -splitQuaternionK := by
  simpa [splitQuaternionI, splitQuaternionJ, splitQuaternionK]
    using (matrix_split_quaternion_basis_laws).2.2.2.2

/-- Explicit matrix form of `a + b ε`. -/
theorem splitComplexMatrix_eq (a b : ℝ) :
    splitComplexMatrix a b = !![a + b, 0; 0, a - b] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [splitComplexMatrix, splitComplexEpsilon, Eplus, Matrix.smul_apply,
      Matrix.add_apply]
    try ring

/-- The split-complex norm/determinant is `a² - b²`. -/
theorem splitComplexMatrix_det (a b : ℝ) :
    Matrix.det (splitComplexMatrix a b) = a ^ 2 - b ^ 2 := by
  rw [splitComplexMatrix_eq]
  simp [Matrix.det_fin_two]
  ring

/-- The two null split-complex directions have zero determinant. -/
theorem splitComplexMatrix_det_self (a : ℝ) :
    Matrix.det (splitComplexMatrix a a) = 0 := by
  simp [splitComplexMatrix_det]

/-- The opposite null split-complex direction has zero determinant. -/
theorem splitComplexMatrix_det_neg_self (a : ℝ) :
    Matrix.det (splitComplexMatrix a (-a)) = 0 := by
  simp [splitComplexMatrix_det]

/-- Explicit matrix form of `w·1 + x·I + y·J + z·K`. -/
theorem splitQuaternionMatrix_eq (w x y z : ℝ) :
    splitQuaternionMatrix w x y z = !![w + z, y + x; y - x, w - z] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitQuaternionMatrix, splitQuaternionI, splitQuaternionJ, splitQuaternionK,
      Eminus, J1, Eplus, Matrix.smul_apply, Matrix.add_apply] <;>
    ring

/-- The split-quaternion determinant/norm has signature `(2,2)`. -/
theorem splitQuaternionMatrix_det (w x y z : ℝ) :
    Matrix.det (splitQuaternionMatrix w x y z) = w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  rw [splitQuaternionMatrix_eq]
  simp [Matrix.det_fin_two]
  ring

/-- A determinant-zero split-quaternion coordinate is a matrix zero divisor. -/
theorem splitQuaternionMatrix_null_det
    {w x y z : ℝ} (h : w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 = 0) :
    Matrix.det (splitQuaternionMatrix w x y z) = 0 := by
  rw [splitQuaternionMatrix_det, h]

/-- Positive split-complex idempotent `(1 + ε)/2`. -/
def splitIdempotentPlus : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) + splitComplexEpsilon)

/-- Negative split-complex idempotent `(1 - ε)/2`. -/
def splitIdempotentMinus : Mat2 :=
  (1 / 2 : ℝ) • ((1 : Mat2) - splitComplexEpsilon)

/-- Positive nilpotent/null hop. -/
def splitNilpotentPlus : Mat2 :=
  matrixCausalNullPlus

/-- Negative nilpotent/null hop. -/
def splitNilpotentMinus : Mat2 :=
  matrixCausalNullMinus

theorem splitIdempotents_explicit :
    splitIdempotentPlus = !![(1 : ℝ), 0; 0, 0]
      ∧ splitIdempotentMinus = !![0, 0; 0, (1 : ℝ)] := by
  exact matrix_krein_projectors_explicit

theorem splitIdempotentPlus_sq :
    splitIdempotentPlus * splitIdempotentPlus = splitIdempotentPlus := by
  have h := splitIdempotents_explicit
  rw [h.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem splitIdempotentMinus_sq :
    splitIdempotentMinus * splitIdempotentMinus = splitIdempotentMinus := by
  have h := splitIdempotents_explicit
  rw [h.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem splitIdempotentPlus_mul_minus :
    splitIdempotentPlus * splitIdempotentMinus = 0 := by
  have h := splitIdempotents_explicit
  rw [h.1, h.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem splitIdempotentMinus_mul_plus :
    splitIdempotentMinus * splitIdempotentPlus = 0 := by
  have h := splitIdempotents_explicit
  rw [h.1, h.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

theorem splitNilpotents_explicit :
    splitNilpotentPlus = !![(0 : ℝ), 1; 0, 0]
      ∧ splitNilpotentMinus = !![0, 0; (1 : ℝ), 0] := by
  simpa [splitNilpotentPlus, splitNilpotentMinus] using matrix_causal_nulls_explicit

theorem splitNilpotentPlus_sq :
    splitNilpotentPlus * splitNilpotentPlus = 0 := by
  simpa [splitNilpotentPlus] using (matrix_causal_null_closure_laws).1

theorem splitNilpotentMinus_sq :
    splitNilpotentMinus * splitNilpotentMinus = 0 := by
  simpa [splitNilpotentMinus] using (matrix_causal_null_closure_laws).2.1

theorem splitNilpotentPlus_mul_minus :
    splitNilpotentPlus * splitNilpotentMinus = splitIdempotentPlus := by
  simpa [splitNilpotentPlus, splitNilpotentMinus]
    using (matrix_causal_null_closure_laws).2.2.1

theorem splitNilpotentMinus_mul_plus :
    splitNilpotentMinus * splitNilpotentPlus = splitIdempotentMinus := by
  simpa [splitNilpotentPlus, splitNilpotentMinus]
    using (matrix_causal_null_closure_laws).2.2.2.1

end

end InfoGeometry.Canonical.SplitQuaternionMatrixModel
