import Mathlib

variable {𝒜 : Type*} [Ring 𝒜]

theorem nilpotent_stabilization (n : ℕ) (N : 𝒜) (h_nil : N * N = 0) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    rw [mul_assoc, h_nil, mul_zero, add_zero, Nat.cast_succ, add_mul, one_mul]
    ring
