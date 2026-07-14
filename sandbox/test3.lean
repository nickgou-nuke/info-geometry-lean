import Mathlib

variable {𝒜 : Type*} [Ring 𝒜]

theorem nilpotent_stabilization (n : ℕ) (N : 𝒜) (h_nil : N * N = 0) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one]
    rw [nsmul_mul, h_nil, nsmul_zero, add_zero]
    rw [← add_assoc, ← add_assoc]
    congr 1
    rw [add_comm N (k • N), ← succ_nsmul']
