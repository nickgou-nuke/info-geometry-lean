import Mathlib

namespace InfoGeometry.Algebra.CuntzTraceConjugation

open Matrix

variable {n : ℕ}

noncomputable def conjug (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    Matrix (Fin n) (Fin n) ℂ :=
  ⅟P * M * P

theorem matrix_trace_conjug
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] :
    Matrix.trace (conjug P M) = Matrix.trace M := by
  unfold conjug
  calc
    Matrix.trace (⅟P * M * P) = Matrix.trace (M * P * ⅟P) := by
      rw [Matrix.mul_assoc]
      exact Matrix.trace_mul_comm (⅟P) (M * P)
    _ = Matrix.trace M := by
      rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one]

theorem matrix_trace_conjug_pow
    (P M : Matrix (Fin n) (Fin n) ℂ) [Invertible P] (k : ℕ) :
    Matrix.trace ((conjug P M) ^ k) = Matrix.trace (M ^ k) := by
  have hpow : (conjug P M) ^ k = conjug P (M ^ k) := by
    induction k with
    | zero => simp [conjug]
    | succ k ih =>
        rw [pow_succ, ih, pow_succ]
        unfold conjug
        calc
          ⅟P * M ^ k * P * (⅟P * M * P) =
              ⅟P * M ^ k * (P * ⅟P) * M * P := by simp only [mul_assoc]
          _ = ⅟P * M ^ k * M * P := by rw [mul_invOf_self, mul_one]
          _ = ⅟P * (M ^ k * M) * P := by simp only [mul_assoc]
  rw [hpow]
  exact matrix_trace_conjug P (M ^ k)

end InfoGeometry.Algebra.CuntzTraceConjugation
