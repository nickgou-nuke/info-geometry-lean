import Mathlib

lemma zmod_val_cross_ne_zero {n : ℕ} [Fact (2 ≤ n)] (u1 u2 v1 v2 : ZMod n)
    (h : u1 * v2 - v1 * u2 ≠ 0) :
    (u1.val : ℂ) * (v2.val : ℂ) - (u2.val : ℂ) * (v1.val : ℂ) ≠ 0 := by
  intro h0
  have h1 : (u1.val : ℤ) * (v2.val : ℤ) - (u2.val : ℤ) * (v1.val : ℤ) = 0 := by exact_mod_cast h0
  have h2 : ((u1.val : ℤ) * (v2.val : ℤ) - (u2.val : ℤ) * (v1.val : ℤ) : ZMod n) = 0 := by rw [h1, Int.cast_zero]
  have h3 : u1 * v2 - u2 * v1 = 0 := by
    calc u1 * v2 - u2 * v1
      _ = (u1.val : ZMod n) * (v2.val : ZMod n) - (u2.val : ZMod n) * (v1.val : ZMod n) := by
        congr 1
        · congr 1 <;> exact (ZMod.nat_cast_zmod_val _).symm
        · congr 1 <;> exact (ZMod.nat_cast_zmod_val _).symm
      _ = ((u1.val : ℤ) : ZMod n) * ((v2.val : ℤ) : ZMod n) - ((u2.val : ℤ) : ZMod n) * ((v1.val : ℤ) : ZMod n) := by push_cast; rfl
      _ = 0 := h2
  have h4 : u1 * v2 - v1 * u2 = 0 := by
    calc u1 * v2 - v1 * u2
      _ = u1 * v2 - u2 * v1 := by ring
      _ = 0 := h3
  exact h h4

