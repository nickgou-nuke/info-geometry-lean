import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Inductive Clifford tripotent stability

Repair of the external Kronecker/tripotent file using Mathlib's Kronecker
multiplication theorem.  The theorem is algebraic: tensoring a tripotent matrix
with an identity block preserves tripotency.
-/

noncomputable section

namespace CliffordInductiveTripotent

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is tripotent if `T³=T`. -/
def IsTripotent (T : Matrix n n ℝ) : Prop := T * (T * T) = T

/-- Tensor/Kronecker inclusion by a `2×2` identity block. -/
def cliffordStep (T : Matrix n n ℝ) : Matrix (n × Fin 2) (n × Fin 2) ℝ :=
  Matrix.kronecker T (1 : Matrix (Fin 2) (Fin 2) ℝ)

/-- Kronecker multiplication by the identity block respects products. -/
theorem cliffordStep_mul (A B : Matrix n n ℝ) :
    cliffordStep (A * B) = cliffordStep A * cliffordStep B := by
  unfold cliffordStep
  simpa using
    (Matrix.mul_kronecker_mul A B (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- The scaling inclusion `T ↦ T ⊗ I₂` preserves tripotency. -/
theorem kronecker_preserves_tripotency (T : Matrix n n ℝ) (hT : IsTripotent T) :
    IsTripotent (cliffordStep T) := by
  unfold IsTripotent at hT ⊢
  rw [← cliffordStep_mul, ← cliffordStep_mul, hT]

#check cliffordStep_mul
#check kronecker_preserves_tripotency

end CliffordInductiveTripotent
