import InfoGeometry.Algebra.AlternativeDerivations

/-!
# Regular-action commutator and the associator

This module isolates the exact operator identity relating left/right regular
multiplication to the nonassociative associator.  It deliberately works over
Mathlib's `NonUnitalNonAssocRing` hierarchy and reuses the regular maps and
alternative-law lemmas owned by `AlternativeDerivations`.
-/

namespace InfoGeometry.Algebra

variable {R A : Type*}
variable [CommRing R]
variable [NonUnitalNonAssocRing A]
variable [Module R A]
variable [IsScalarTower R A A]
variable [SMulCommClass R A A]

/-- The commutator between left multiplication by `x` and right multiplication by `y`. -/
def leftRightCommutator (x y : A) : A →ₗ[R] A :=
  (L_map (R := R) x).comp (R_map (R := R) y) -
    (R_map (R := R) y).comp (L_map (R := R) x)

/-- Generic nonassociative identity `[L_x,R_y] z = - associator x z y`. -/
theorem leftRightCommutator_apply (x y z : A) :
    leftRightCommutator (R := R) x y z = -associator x z y := by
  change x * (z * y) - (x * z) * y = -((x * z) * y - x * (z * y))
  abel

/--
In a right-alternative ring, the mixed regular commutator evaluates to the
associator in the natural order.
-/
theorem leftRightCommutator_apply_of_right_alternative
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    leftRightCommutator (R := R) x y z = associator x y z := by
  rw [leftRightCommutator_apply]
  rw [alternative_associator_swap23 hright x y z]

/-- Alias for `leftRightCommutator_apply_of_right_alternative`. -/
theorem leftRightCommutator_apply_of_alternative
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y z : A) :
    leftRightCommutator (R := R) x y z = associator x y z :=
  leftRightCommutator_apply_of_right_alternative hright x y z

/--
Under the two alternative laws, `(x,y) ↦ [L_x,R_y]` is alternating as an
endomorphism-valued bilinear obstruction.
-/
theorem leftRightCommutator_swap
    (hleft : ∀ x y : A, (x * x) * y = x * (x * y))
    (hright : ∀ x y : A, (y * x) * x = y * (x * x))
    (x y : A) :
    leftRightCommutator (R := R) y x = -leftRightCommutator (R := R) x y := by
  apply LinearMap.ext
  intro z
  change leftRightCommutator (R := R) y x z =
    -leftRightCommutator (R := R) x y z
  rw [leftRightCommutator_apply_of_right_alternative (R := R) hright y x z,
    leftRightCommutator_apply_of_right_alternative (R := R) hright x y z]
  exact alternative_associator_swap12 hleft y x z

/-- The mixed regular commutator is zero whenever the relevant associator vanishes. -/
theorem leftRightCommutator_eq_zero_of_associator
    (x y : A)
    (hassoc : ∀ z : A, associator x z y = 0) :
    leftRightCommutator (R := R) x y = 0 := by
  apply LinearMap.ext
  intro z
  rw [leftRightCommutator_apply, hassoc z]
  simp

/--
Right multiplication by `y` commutes with every left multiplication exactly
when `y` has zero associator in the third slot.
-/
theorem rightRegular_commutes_with_all_left_iff (y : A) :
    (∀ x : A,
        (L_map (R := R) x).comp (R_map (R := R) y) =
          (R_map (R := R) y).comp (L_map (R := R) x)) ↔
      (∀ x z : A, associator x z y = 0) := by
  constructor
  · intro h x z
    have hz := congrArg (fun F : A →ₗ[R] A => F z) (h x)
    change x * (z * y) = (x * z) * y at hz
    simpa [associator_apply] using sub_eq_zero.mpr hz.symm
  · intro h x
    apply LinearMap.ext
    intro z
    have hassoc : associator x z y = 0 := h x z
    change x * (z * y) = (x * z) * y
    simpa [associator_apply] using (sub_eq_zero.mp hassoc).symm

end InfoGeometry.Algebra
