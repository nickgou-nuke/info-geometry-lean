import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Pullback of star structure across an algebra equivalence

An algebra equivalence into a star algebra canonically transports the
involution back to its source.  This small reusable construction packages the
transported `StarRing` structure and exposes the defining
intertwining identity.
-/

noncomputable section

namespace StarAlgEquivPullback

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
variable [CommSemiring R]
variable [NormedRing A] [NormedRing B]
variable [Algebra R A] [Algebra R B]

/-- Pull back a full star-ring structure along an algebra equivalence. -/
def starRing [StarRing B] (e : A ≃ₐ[R] B) : StarRing A where
  star x := e.symm (star (e x))
  star_involutive x := by
    apply e.injective
    simp
  star_add x y := by
    apply e.injective
    simp
  star_mul x y := by
    apply e.injective
    simp

/-- The defining intertwining identity for the pulled-back involution. -/
theorem starRing_map_star [StarRing B] (e : A ≃ₐ[R] B) (x : A) :
    letI : StarRing A := starRing e
    e (star x) = star (e x) := by
  exact e.apply_symm_apply _

/-- Pull the C-star norm inequality back along an isometric algebra
equivalence.  This is the normed counterpart of `starRing`: no pointwise
reconstruction of the C-star law is needed downstream. -/
theorem norm_mul_self_le [StarRing B] [CStarRing B]
    (e : A ≃ₐ[R] B) (hnorm : ∀ x : A, ‖e x‖ = ‖x‖) (x : A) :
    letI : StarRing A := starRing e
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  letI : StarRing A := starRing e
  calc
    ‖x‖ * ‖x‖ = ‖e x‖ * ‖e x‖ := by rw [hnorm]
    _ ≤ ‖star (e x) * e x‖ := CStarRing.norm_mul_self_le (e x)
    _ = ‖e (star x) * e x‖ := by
      rw [starRing_map_star]
    _ = ‖e (star x * x)‖ := by rw [map_mul]
    _ = ‖star x * x‖ := hnorm _

end StarAlgEquivPullback
