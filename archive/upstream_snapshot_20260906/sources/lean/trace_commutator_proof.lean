import Mathlib

open Matrix
open scoped Matrix

-- Theorem: trace([A, B]) = 0 for any square matrices over a commutative ring
theorem trace_commutator_zero {n : ℕ} {R : Type _} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) : trace (A * B - B * A) = 0 :=
by
  calc
    trace (A * B - B * A) = trace (A * B) - trace (B * A) := by
      simp
    _ = trace (A * B) - trace (A * B) := by
      rw [trace_mul_comm A B]
    _ = 0 := by ring

#check trace_commutator_zero
