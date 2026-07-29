import Mathlib.Algebra.Star.StarAlgHom

/-!
# Structural transport of star-algebra representations

This is the algebraic functoriality used when a representation is moved across
a star-algebra equivalence.  Composition supplies all homomorphism laws; the
API deliberately exposes no coordinate or norm-level surrogate.
-/

namespace StarAlgEquivTransport

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Star A]
variable [Semiring B] [Algebra R B] [Star B]
variable [Semiring C] [Algebra R C] [Star C]

/-- Transport a star-algebra representation through a star-algebra
equivalence. -/
def map (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B) : A →⋆ₐ[R] C :=
  (e : B →⋆ₐ[R] C).comp π

@[simp] theorem map_apply (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B) (a : A) :
    map e π a = e (π a) :=
  rfl

@[simp] theorem map_star (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B) (a : A) :
    map e π (star a) = star (map e π a) :=
  by
    change e (π (star a)) = star (e (π a))
    rw [map_star]
    exact map_star e (π a)

@[simp] theorem map_mul (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B)
    (a b : A) :
    map e π (a * b) = map e π a * map e π b :=
  by
    change e (π (a * b)) = e (π a) * e (π b)
    rw [map_mul, map_mul]

end StarAlgEquivTransport
