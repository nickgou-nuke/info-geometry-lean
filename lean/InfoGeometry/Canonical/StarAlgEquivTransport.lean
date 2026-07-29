import Mathlib.Algebra.Star.StarAlgHom

/-!
# Structural transport of star-algebra representations

This is the algebraic functoriality used when a representation is moved across
a star-algebra equivalence.  Composition supplies all homomorphism laws; the
API deliberately exposes no coordinate or norm-level surrogate.
-/

namespace StarAlgEquivTransport

universe uR uA uB uC uD

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
variable [CommSemiring R]
variable [Semiring A] [Algebra R A] [Star A]
variable [Semiring B] [Algebra R B] [Star B]
variable [Semiring C] [Algebra R C] [Star C]
variable [Semiring D] [Algebra R D] [Star D]

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
    calc
      e (π (star a)) = e (star (π a)) := by rw [StarHomClass.map_star π]
      _ = star (e (π a)) := StarHomClass.map_star e (π a)

@[simp] theorem map_mul (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B)
    (a b : A) :
    map e π (a * b) = map e π a * map e π b :=
  by
    change e (π (a * b)) = e (π a) * e (π b)
    calc
      e (π (a * b)) = e (π a * π b) := congrArg e (π.map_mul' a b)
      _ = e (π a) * e (π b) := e.toAlgEquiv.map_mul _ _

/-- Transport is coherent with composition of star-algebra equivalences. -/
theorem map_trans (e₁ : B ≃⋆ₐ[R] C) (e₂ : C ≃⋆ₐ[R] D)
    (π : A →⋆ₐ[R] B) :
    map e₂ (map e₁ π) = map (e₁.trans e₂) π := by
  ext a
  rfl

/-- Transport along the identity equivalence is the original representation. -/
theorem map_refl (π : A →⋆ₐ[R] B) :
    map (StarAlgEquiv.refl : B ≃⋆ₐ[R] B) π = π := by
  ext a
  rfl

/-- Transport along an equivalence and then its inverse returns the original
representation. -/
theorem map_symm_map (e : B ≃⋆ₐ[R] C) (π : A →⋆ₐ[R] B) :
    map e.symm (map e π) = π := by
  ext a
  simp

end StarAlgEquivTransport
