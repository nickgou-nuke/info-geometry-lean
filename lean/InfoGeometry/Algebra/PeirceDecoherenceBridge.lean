import Mathlib

namespace InfoGeometry.Algebra

section Peirce

variable {A : Type*} [Ring A]

/-- An element is idempotent if its square is itself. -/
def IsIdempotent (e : A) : Prop :=
  e * e = e

/-- 
The Peirce Decoherence Annihilation.
When the off-diagonal entangled sector `e * X * (1 - e)` is subjected to 
the idempotent measurement projector `e` from both sides, it collapses to zero.
-/
theorem peirce_off_diagonal_annihilation (e x : A) (he : IsIdempotent e) :
    e * (e * x * (1 - e)) * e = 0 := by
  calc
    e * (e * x * (1 - e)) * e 
      _ = (e * e) * x * (1 - e) * e := by ring
    _ = e * x * (1 - e) * e := by rw [he]
    _ = e * x * (e - e * e) := by ring
    _ = e * x * (e - e) := by rw [he]
    _ = e * x * 0 := by rw [sub_self]
    _ = 0 := by ring

end Peirce

end InfoGeometry.Algebra
