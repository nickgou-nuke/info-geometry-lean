import Mathlib

namespace InfoGeometry.Algebra

section Peirce

variable {A : Type*} [Ring A]

/-- An idempotent sandwich with its complementary factor vanishes in any ring.
This is the algebraic identity `e * (e * x * (1 - e)) * e = 0`. -/
theorem idempotent_off_diagonal_sandwich_zero (e x : A)
    (he : IsIdempotentElem e) :
    e * (e * x * (1 - e)) * e = 0 := by
  calc
    e * (e * x * (1 - e)) * e = e * e * x * ((1 - e) * e) := by
      simp only [mul_assoc]
    _ = e * x * ((1 - e) * e) := by rw [he.eq]
    _ = e * x * 0 := by
      rw [sub_mul, one_mul, he.eq, sub_self]
    _ = 0 := by simp

end Peirce

end InfoGeometry.Algebra
