import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Discretionary Hodge Star

Formalization of the discretionary Hodge star operator.
In the discrete/cellular setting, the Hodge star is an explicit linear isomorphism
mapping cochains to their duals without relying on smooth metric measure spaces.
-/

namespace InfoGeometry.Physics.Hodge

-- A vector space of discrete forms.
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- 
The discretionary Hodge star is a linear involution (up to sign depending on signature)
on the space of discrete forms V.
Here we define the generic structure of a discretionary Hodge star.
-/
structure DiscretionaryHodgeStar (V : Type*) [AddCommGroup V] [Module ℝ V] where
  star : V →ₗ[ℝ] V
  is_involution : ∀ v, star (star v) = v ∨ star (star v) = -v

/-- 
If the Hodge star squares to the identity, it preserves the space pointwise upon double application.
-/
theorem discretionary_hodge_star_square_id
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : DiscretionaryHodgeStar V) (h_pos : ∀ v, H.star (H.star v) = v) (x : V) :
    H.star (H.star x) = x :=
  h_pos x

/-- 
If the Hodge star squares to minus the identity, we get the standard Lorentzian middle-degree behavior.
-/
theorem discretionary_hodge_star_square_neg
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (H : DiscretionaryHodgeStar V) (h_neg : ∀ v, H.star (H.star v) = -v) (x : V) :
    H.star (H.star x) = -x :=
  h_neg x

end InfoGeometry.Physics.Hodge
