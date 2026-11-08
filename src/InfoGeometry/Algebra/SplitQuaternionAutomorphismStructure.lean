import InfoGeometry.Algebra.SplitQuaternionMatrices
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Split-quaternion automorphism and structure algebra

Let `Mat2 = Matrix (Fin 2) (Fin 2) ℝ` and

`det₂ [[a,b],[c,d]] = a*d - b*c`.

This module proves the exact finite algebra underlying the split-quaternion
matrix model:

* the adjugate inverse formula for `2 × 2` matrices;
* inner conjugation `X ↦ A X A⁻¹` is multiplicative and determinant preserving
  whenever `det₂ A ≠ 0`;
* left-right transformations `X ↦ A X B` scale determinant by
  `det₂ A * det₂ B`;
* transpose preserves determinant and reverses multiplication order;
* the trace-zero split-quaternion coordinate plane has determinant
  `y^2 - x^2 - z^2`, the `(1,2)` quadratic form.

All statements are over the concrete `M₂(ℝ)` owner model.
-/

noncomputable section

namespace InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure

open Matrix
open InfoGeometry.Algebra.SplitQuaternionMatrices

abbrev Mat2 : Type := InfoGeometryCore.M2R

/-- The classical adjugate of a `2 × 2` matrix. -/
def adj2 (A : Mat2) : Mat2 :=
  !![A 1 1, -A 0 1;
     -A 1 0, A 0 0]

/-- The explicit inverse matrix `det(A)⁻¹ adj(A)`. -/
def inv2 (A : Mat2) : Mat2 :=
  (det2 A)⁻¹ • adj2 A

/-- Inner conjugation by an invertible `2 × 2` matrix. -/
def innerConj (A X : Mat2) : Mat2 :=
  A * X * inv2 A

/-- Left-right structure transformation. -/
def leftRight (A B X : Mat2) : Mat2 :=
  A * X * B

/-- Trace-zero split-quaternion coordinate matrix. -/
def traceZeroMatrix (x y z : ℝ) : Mat2 :=
  !![z, x + y;
     x - y, -z]

@[simp]
theorem adj2_apply00 (A : Mat2) : adj2 A 0 0 = A 1 1 := rfl

@[simp]
theorem adj2_apply01 (A : Mat2) : adj2 A 0 1 = -A 0 1 := rfl

@[simp]
theorem adj2_apply10 (A : Mat2) : adj2 A 1 0 = -A 1 0 := rfl

@[simp]
theorem adj2_apply11 (A : Mat2) : adj2 A 1 1 = A 0 0 := rfl

/-- `A adj(A) = det(A) I`. -/
theorem mul_adj2 (A : Mat2) :
    A * adj2 A = (det2 A) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, det2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- `adj(A) A = det(A) I`. -/
theorem adj2_mul (A : Mat2) :
    adj2 A * A = (det2 A) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, det2, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Right inverse law for the explicit inverse. -/
theorem mul_inv2 (A : Mat2) (hA : det2 A ≠ 0) :
    A * inv2 A = (1 : Mat2) := by
  calc
    A * inv2 A = (det2 A)⁻¹ • (A * adj2 A) := by
      simp [inv2]
    _ = (det2 A)⁻¹ • ((det2 A) • (1 : Mat2)) := by rw [mul_adj2]
    _ = (1 : Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
      all_goals field_simp [hA]

/-- Left inverse law for the explicit inverse. -/
theorem inv2_mul (A : Mat2) (hA : det2 A ≠ 0) :
    inv2 A * A = (1 : Mat2) := by
  calc
    inv2 A * A = (det2 A)⁻¹ • (adj2 A * A) := by
      simp [inv2]
    _ = (det2 A)⁻¹ • ((det2 A) • (1 : Mat2)) := by rw [adj2_mul]
    _ = (1 : Mat2) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
      all_goals field_simp [hA]

/-- Determinant of the explicit inverse. -/
theorem det2_inv2 (A : Mat2) (hA : det2 A ≠ 0) :
    det2 (inv2 A) = (det2 A)⁻¹ := by
  have hmul := det2_mul A (inv2 A)
  rw [mul_inv2 A hA] at hmul
  have hdet_one : det2 (1 : Mat2) = 1 := by
    unfold det2
    simp
  rw [hdet_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

/-- Inner conjugation preserves multiplication. -/
theorem innerConj_mul (A X Y : Mat2) (hA : det2 A ≠ 0) :
    innerConj A (X * Y) = innerConj A X * innerConj A Y := by
  unfold innerConj
  calc
    A * (X * Y) * inv2 A = A * X * (Y * inv2 A) := by noncomm_ring
    _ = A * X * ((inv2 A * A) * Y * inv2 A) := by rw [inv2_mul A hA]; noncomm_ring
    _ = (A * X * inv2 A) * (A * Y * inv2 A) := by noncomm_ring

/-- Inner conjugation fixes the identity. -/
theorem innerConj_one (A : Mat2) (hA : det2 A ≠ 0) :
    innerConj A (1 : Mat2) = 1 := by
  unfold innerConj
  simpa [mul_assoc] using mul_inv2 A hA

/-- Inner conjugation preserves the split-quaternion determinant. -/
theorem det2_innerConj (A X : Mat2) (hA : det2 A ≠ 0) :
    det2 (innerConj A X) = det2 X := by
  unfold innerConj
  rw [det2_mul, det2_mul, det2_inv2 A hA]
  field_simp [hA]

/-- Left-right structure transformations scale determinant by the character `det A * det B`. -/
theorem det2_leftRight (A B X : Mat2) :
    det2 (leftRight A B X) = (det2 A * det2 B) * det2 X := by
  unfold leftRight
  rw [det2_mul, det2_mul]
  ring

/-- Transposition preserves the coordinate determinant. -/
theorem det2_transpose (X : Mat2) :
    det2 X.transpose = det2 X := by
  unfold det2
  simp
  ring

/-- Transposition reverses multiplication order. -/
theorem transpose_mul_reverse (X Y : Mat2) :
    (X * Y).transpose = Y.transpose * X.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- Trace of the trace-zero coordinate matrix is zero. -/
theorem trace2_traceZeroMatrix (x y z : ℝ) :
    trace2 (traceZeroMatrix x y z) = 0 := by
  unfold trace2 traceZeroMatrix
  simp

/-- The determinant on trace-zero split quaternions is the `(1,2)` form. -/
theorem det2_traceZeroMatrix (x y z : ℝ) :
    det2 (traceZeroMatrix x y z) = y ^ 2 - x ^ 2 - z ^ 2 := by
  unfold det2 traceZeroMatrix
  simp
  ring

/-- The determinant on all split-quaternion coordinates is the `(2,2)` form. -/
theorem det2_splitQuaternion_signature (w x y z : ℝ) :
    det2 (splitQ w x y z) = w ^ 2 + x ^ 2 - y ^ 2 - z ^ 2 := by
  rw [det2_splitQ]
  ring

/-- Structure packet for left-right and transpose determinant similitudes. -/
theorem structure_group_generators_packet (A B X : Mat2) :
    det2 (leftRight A B X) = (det2 A * det2 B) * det2 X ∧
      det2 X.transpose = det2 X :=
  ⟨det2_leftRight A B X, det2_transpose X⟩

/-- Automorphism packet for one inner conjugation. -/
theorem inner_automorphism_packet (A : Mat2) (hA : det2 A ≠ 0) :
    innerConj A (1 : Mat2) = 1 ∧
      (∀ X Y : Mat2, innerConj A (X * Y) = innerConj A X * innerConj A Y) ∧
      (∀ X : Mat2, det2 (innerConj A X) = det2 X) :=
  ⟨innerConj_one A hA, fun X Y => innerConj_mul A X Y hA, fun X => det2_innerConj A X hA⟩

end InfoGeometry.Algebra.SplitQuaternionAutomorphismStructure
