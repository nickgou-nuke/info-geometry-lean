import Mathlib

section NonAssociative

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- The associator in a non-associative ring. -/
def associator (x y z : A) : A :=
  (x * y) * z - x * (y * z)

end NonAssociative

section Associative

variable {B : Type*} [NonUnitalRing B]

/-- A Casimir element is one that commutes with all elements. -/
def IsCasimir (C : B) : Prop :=
  ∀ x : B, C * x = x * C

/-- An element is idempotent if its square is itself. -/
def IsIdempotent (e : B) : Prop :=
  e * e = e

/-- If C is a Casimir element and e is an idempotent, then e * C * e = C * e. -/
theorem casimir_survival (C e : B) (hC : IsCasimir C) (he : IsIdempotent e) :
    e * C * e = C * e := by
  calc
    e * C * e = (e * C) * e := rfl
    _ = (C * e) * e := by rw [hC e]
    _ = C * (e * e) := by rw [mul_assoc]
    _ = C * e := by rw [he]

end Associative
