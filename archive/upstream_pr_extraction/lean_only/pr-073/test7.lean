import Mathlib

variable {A : Type*} [Ring A] [Algebra ℂ A]

def anticomm (x y : A) : A := x * y + y * x

lemma anticomm_expand (x1 x2 y1 y2 : A) (c1 c2 d1 d2 : ℂ) :
  anticomm (c1 • x1 + c2 • x2) (d1 • y1 + d2 • y2) =
  (c1 * d1) • anticomm x1 y1 + (c1 * d2) • anticomm x1 y2 +
  (c2 * d1) • anticomm x2 y1 + (c2 * d2) • anticomm x2 y2 := by
  dsimp [anticomm]
  -- noncomm_ring doesn't do smul, but we can pull out smuls
  -- Actually, simp [smul_add, add_smul, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_smul] should do it
  simp [smul_add, add_smul, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  abel

