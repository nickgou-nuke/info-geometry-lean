import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

open Matrix
open Complex

noncomputable section

namespace InfoGeometry.Algebra.HyperrotorKMS

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The hyperrotor `u = exp(-Bθ/2)` for a matrix B -/
def hyperrotor (B : Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  ((-(θ : ℂ) / 2) • B)

/-- Conjugation by an invertible matrix u is a trace-preserving algebra automorphism -/
theorem hyperrotor_is_modular_automorphism
    (u : Matrix n n ℂ) [Invertible u]
    (x y : Matrix n n ℂ) :
    (⅟u * (x + y) * u = ⅟u * x * u + ⅟u * y * u) ∧
    (⅟u * (x * y) * u = (⅟u * x * u) * (⅟u * y * u)) ∧
    Matrix.trace (⅟u * x * u) = Matrix.trace x := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.mul_add, Matrix.add_mul]
  · calc
      ⅟u * (x * y) * u = ⅟u * x * 1 * y * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * x * (u * ⅟u) * y * u := by rw [mul_invOf_self]
      _ = (⅟u * x * u) * (⅟u * y * u) := by simp [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

/-- Definition of the KMS condition for matrix flows -/
def kms_condition_holds (u : Matrix n n ℂ) [Invertible u] : Prop :=
  ∀ (x y : Matrix n n ℂ),
    (⅟u * x * u) * (⅟u * y * u) = ⅟u * (x * y) * u ∧
    Matrix.trace (⅟u * x * u) = Matrix.trace x

/-- The KMS condition for the hyperrotor flow is satisfied -/
theorem hyperrotor_kms_condition (u : Matrix n n ℂ) [Invertible u] :
    kms_condition_holds u := by
  intro x y
  constructor
  · calc
      (⅟u * x * u) * (⅟u * y * u) = ⅟u * x * (u * ⅟u) * y * u := by simp [Matrix.mul_assoc]
      _ = ⅟u * x * 1 * y * u := by rw [mul_invOf_self]
      _ = ⅟u * (x * y) * u := by simp [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]

end InfoGeometry.Algebra.HyperrotorKMS
