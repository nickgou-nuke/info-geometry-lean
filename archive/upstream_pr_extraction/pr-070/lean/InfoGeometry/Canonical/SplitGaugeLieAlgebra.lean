import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import InfoGeometry.Canonical.SplitGaugeGroup

namespace InfoGeometry.Canonical

variable (R : Type*) [CommRing R]

/-- 
  The Lie Algebra 𝔰𝔬(5,5) is the space of matrices X satisfying:
  X * η + η * Xᵀ = 0
-/
def is_so55_lie_algebra (X : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R) : Prop :=
  X * (splitMetric10D R) + (splitMetric10D R) * X.transpose = 0

/-- Commutator of two matrices [X, Y] = X*Y - Y*X -/
def matrix_commutator (X Y : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R) : 
    Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R :=
  X * Y - Y * X

/-- 
  Theorem: The Lie algebra 𝔰𝔬(5,5) is closed under the commutator.
  If X, Y ∈ 𝔰𝔬(5,5), then [X, Y] ∈ 𝔰𝔬(5,5).
-/
theorem so55_lie_algebra_closure 
    (X Y : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R)
    (hX : is_so55_lie_algebra R X)
    (hY : is_so55_lie_algebra R Y) : 
    is_so55_lie_algebra R (matrix_commutator R X Y) := by
  dsimp [is_so55_lie_algebra, matrix_commutator]
  
  -- Step 1: Expand the transpose
  rw [Matrix.transpose_sub]
  rw [Matrix.transpose_mul]
  rw [Matrix.transpose_mul]
  
  -- Step 2: Expand multiplications over subtraction
  rw [Matrix.sub_mul]
  rw [Matrix.mul_sub]
  
  have hX_eq : X * splitMetric10D R = -(splitMetric10D R * X.transpose) := eq_neg_of_add_eq_zero_left hX
  have hY_eq : Y * splitMetric10D R = -(splitMetric10D R * Y.transpose) := eq_neg_of_add_eq_zero_left hY
  
  -- Matrix associativity: X * Y * η = X * (Y * η)
  rw [Matrix.mul_assoc X Y (splitMetric10D R)]
  rw [hY_eq]
  rw [Matrix.mul_neg]
  
  rw [Matrix.mul_assoc Y X (splitMetric10D R)]
  rw [hX_eq]
  rw [Matrix.mul_neg]
  
  -- Use associativity again
  rw [← Matrix.mul_assoc X (splitMetric10D R) Y.transpose]
  rw [← Matrix.mul_assoc Y (splitMetric10D R) X.transpose]
  
  -- Substitute X*η and Y*η
  rw [hX_eq]
  rw [hY_eq]
  
  rw [Matrix.neg_mul]
  rw [neg_neg]
  rw [Matrix.neg_mul]
  rw [neg_neg]
  
  rw [← Matrix.mul_assoc (splitMetric10D R) Y.transpose X.transpose]
  rw [← Matrix.mul_assoc (splitMetric10D R) X.transpose Y.transpose]
  
  -- A - B + (B - A) = 0
  abel
  
end InfoGeometry.Canonical
