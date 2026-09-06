import InfoGeometry.Canonical.OperatorZornCoefficientNucleus

/-!
# All finite coefficient Peirce sectors of the full operator-Zorn carrier

The matrix dimension and coefficient ring are arbitrary. Matrix multiplication
is used only inside the coefficient algebra. All n^2 field sectors are retained.
-/

noncomputable section
namespace InfoGeometry.Canonical.OperatorZornMatrixPeirce

open OperatorZornCoefficientNucleus
open scoped BigOperators Matrix

variable {J B : Type*} [Fintype J] [DecidableEq J] [Ring B]

def coefficientProjector (k : J) : Matrix J J B :=
  Matrix.diagonal (fun i => if i = k then 1 else 0)

theorem coefficientProjector_mul_apply (k : J) (M : Matrix J J B) (i j : J) :
    (coefficientProjector k * M) i j = if i = k then M i j else 0 := by
  by_cases h : i = k <;>
    simp [coefficientProjector, Matrix.mul_apply, Matrix.diagonal, h]

theorem mul_coefficientProjector_apply (M : Matrix J J B) (k i j : J) :
    (M * coefficientProjector k) i j = if j = k then M i j else 0 := by
  by_cases h : j = k <;>
    simp [coefficientProjector, Matrix.mul_apply, Matrix.diagonal, h, eq_comm]

theorem coefficientProjector_product (j k : J) :
    coefficientProjector (B := B) j * coefficientProjector k =
      if j = k then coefficientProjector k else 0 := by
  ext a b
  rw [coefficientProjector_mul_apply]
  by_cases hjk : j = k
  · subst k
    by_cases h : a = j <;> simp [coefficientProjector, Matrix.diagonal, h]
  · by_cases h : a = j
    · subst a
      simp [hjk, coefficientProjector, Matrix.diagonal]
    · simp [hjk, h]

@[simp] theorem coefficientProjector_idempotent (k : J) :
    coefficientProjector (B := B) k * coefficientProjector k = coefficientProjector k := by
  rw [coefficientProjector_product, if_pos rfl]

theorem coefficientProjector_orthogonal (j k : J) (h : j ≠ k) :
    coefficientProjector (B := B) j * coefficientProjector k = 0 := by
  rw [coefficientProjector_product, if_neg h]

theorem coefficientProjector_complete :
    (∑ k : J, coefficientProjector (B := B) k) = 1 := by
  ext a b
  by_cases h : a = b
  · subst b
    simp [coefficientProjector, Matrix.diagonal]
  · simp [coefficientProjector, Matrix.diagonal, h]

section Zorn
variable [Algebra ℝ B]

def matrixSector (j k : J) (X : OperatorZornMatrix (Matrix J J B)) :
    OperatorZornMatrix (Matrix J J B) :=
  corner (coefficientProjector j) (coefficientProjector k) X

theorem matrixSector_reconstruction (X : OperatorZornMatrix (Matrix J J B)) :
    (∑ j : J, ∑ k : J, matrixSector j k X) = X :=
  corner_reconstruction coefficientProjector coefficientProjector_complete X

theorem matrixSector_product_zero (j k l m : J) (h : k ≠ l)
    (X Y : OperatorZornMatrix (Matrix J J B)) :
    matrixSector j k X * matrixSector l m Y = 0 :=
  corner_product_zero _ _ _ _ (coefficientProjector_orthogonal k l h) X Y

theorem matrixSector_product_matching (j k m : J)
    (X Y : OperatorZornMatrix (Matrix J J B)) :
    matrixSector j k X * matrixSector k m Y =
      matrixSector j m (X * (diagonalCoefficient (coefficientProjector k) * Y)) := by
  unfold matrixSector
  rw [corner_product, coefficientProjector_idempotent]

end Zorn
end InfoGeometry.Canonical.OperatorZornMatrixPeirce
