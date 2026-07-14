import Mathlib

variable {𝒜 : Type*} [Ring 𝒜]

theorem nilpotent_stabilization (n : ℕ) (N : 𝒜) (h_nil : N * N = 0) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one]
    rw [nsmul_eq_mul, nsmul_eq_mul]
    -- We have 1 + N + (k : 𝒜) * N + ((k : 𝒜) * N) * N
    rw [mul_assoc]
    rw [h_nil]
    rw [mul_zero, add_zero]
    -- We have 1 + N + (k : 𝒜) * N
    -- and goal is 1 + ((k + 1) : 𝒜) * N
    rw [Nat.cast_succ]
    rw [add_mul, one_mul]
    rw [← add_assoc, add_comm N ((k : 𝒜) * N), add_assoc]
