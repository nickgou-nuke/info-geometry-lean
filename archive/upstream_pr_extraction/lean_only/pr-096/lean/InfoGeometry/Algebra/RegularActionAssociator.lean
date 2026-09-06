import Mathlib.Algebra.Ring.Associator
import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Regular-action commutator and the associator

This module adds only the missing operator bridge.  The regular actions,
nonassociative derivations, alternativity lemmas, and Zorn associator owner are
imported from their native modules.
-/

namespace InfoGeometry.Algebra

variable {R A : Type*}
variable [CommRing R]
variable [NonUnitalNonAssocRing A]
variable [Module R A]
variable [IsScalarTower R A A]
variable [SMulCommClass R A A]

/-- The commutator of left multiplication by `x` and right multiplication by `y`. -/
def leftRightCommutator (x y : A) : A →ₗ[R] A :=
  (L_map (R := R) x).comp (R_map (R := R) y) -
    (R_map (R := R) y).comp (L_map (R := R) x)

/--
For every nonassociative ring in the native Mathlib hierarchy,
`[L_x,R_y] z` is the negative associator with the final two slots exchanged.
-/
theorem leftRightCommutator_apply (x y z : A) :
    leftRightCommutator (R := R) x y z = -associator x z y := by
  unfold leftRightCommutator
  simp [LinearMap.sub_apply, LinearMap.comp_apply, L_map, R_map, associator_apply]

/--
Under right alternativity, the regular-action commutator evaluates directly to
the associator: `[L_x,R_y] z = associator x y z`.
-/
theorem leftRightCommutator_apply_of_right_alternative
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    leftRightCommutator (R := R) x y z = associator x y z := by
  rw [leftRightCommutator_apply]
  have hswap := alternative_associator_swap23 hright x z y
  simp [hswap, neg_neg]

/--
For an alternative multiplication, the operator-valued map
`(x,y) ↦ [L_x,R_y]` is alternating in its two parameters.
-/
theorem leftRightCommutator_swap
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y : A) :
    leftRightCommutator (R := R) y x = -leftRightCommutator (R := R) x y := by
  ext z
  rw [LinearMap.neg_apply]
  rw [leftRightCommutator_apply_of_right_alternative hright y x z,
    leftRightCommutator_apply_of_right_alternative hright x y z]
  exact alternative_associator_swap12 hleft y x z

/-- In an alternative algebra, the diagonal regular-action commutator vanishes. -/
theorem leftRightCommutator_self
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x : A) :
    leftRightCommutator (R := R) x x = 0 := by
  ext z
  rw [leftRightCommutator_apply_of_right_alternative hright x x z]
  simp only [associator_apply]
  rw [hleft]
  simp

namespace ZornVectorMatrix

/-- Canonical Zorn specialization of the regular-action/associator identity. -/
theorem zorn_leftRightCommutator_apply
    (x y z : ZornVectorMatrix R) :
    leftRightCommutator (R := R) x y z = _root_.associator x y z := by
  exact leftRightCommutator_apply_of_right_alternative
    (R := R) zorn_right_alternative x y z

/-- Canonical Zorn regular-action commutator is alternating in its parameters. -/
theorem zorn_leftRightCommutator_swap
    (x y : ZornVectorMatrix R) :
    leftRightCommutator (R := R) y x = -leftRightCommutator (R := R) x y := by
  exact leftRightCommutator_swap
    (R := R)
    zorn_left_alternative
    zorn_right_alternative
    x y

/-- Canonical Zorn diagonal regular-action commutator vanishes. -/
theorem zorn_leftRightCommutator_self
    (x : ZornVectorMatrix R) :
    leftRightCommutator (R := R) x x = 0 := by
  exact leftRightCommutator_self
    (R := R)
    zorn_left_alternative
    zorn_right_alternative
    x

end ZornVectorMatrix

end InfoGeometry.Algebra
