import Mathlib.Algebra.Star.StarAlgHom

/-!
# Pullback of star structure across an algebra equivalence

An algebra equivalence into a star algebra canonically transports the
involution back to its source.  This small reusable construction packages the
transported `Star` and `StarRing` structures and exposes the defining
intertwining identity.
-/

noncomputable section

namespace StarAlgEquivPullback

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommSemiring R]
variable [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra R B]

/-- Pull back an involution along an algebra equivalence. -/
def star [Star B] (e : A ≃ₐ[R] B) : Star A where
  star x := e.symm (star (e x))

/-- The defining intertwining identity for the pulled-back involution. -/
theorem map_star [Star B] (e : A ≃ₐ[R] B) (x : A) :
    e (@star A (star e) x) = star (e x) := by
  exact e.apply_symm_apply _

/-- Pull back a full star-ring structure along an algebra equivalence. -/
def starRing [StarRing B] (e : A ≃ₐ[R] B) :
    @StarRing A _ (star e) where
  star_involutive x := by
    apply e.injective
    rw [map_star, map_star, star_star]
  star_add x y := by
    apply e.injective
    rw [map_star, map_add, star_add, map_add, map_star, map_star]
  star_mul x y := by
    apply e.injective
    rw [map_star, map_mul, star_mul, map_mul, map_star, map_star]

end StarAlgEquivPullback
