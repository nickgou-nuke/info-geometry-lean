import InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

/-!
# Native linear-equivalence package for the coordinate Hodge star

The repository already proves the explicit three-dimensional exterior-coordinate
Hodge involution

`(a, v, φ, d) ↦ (d, φ, v, a)`.

This file does not claim a generic metric Hodge-star construction in Mathlib.
It only upgrades the existing proved involution to Mathlib's native
`LinearEquiv`, so inverse/transport arguments can use the standard equivalence
API rather than re-proving bijectivity.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

/-- Pointwise involutivity of the existing coordinate Hodge star. -/
theorem hodgeStar_involutive : Function.Involutive hodgeStar := by
  intro x
  ext <;> simp [hodgeStar]

/-- Hence the coordinate Hodge star is bijective. -/
theorem hodgeStar_bijective : Function.Bijective hodgeStar :=
  ⟨hodgeStar_involutive.injective, hodgeStar_involutive.surjective⟩

/-- The existing coordinate Hodge star as Mathlib's native real linear
equivalence.  Its inverse is definitionally the same Hodge star. -/
noncomputable def hodgeStarLinearEquiv : Coord ≃ₗ[ℝ] Coord :=
  { hodgeStar with
    invFun := hodgeStar
    left_inv := hodgeStar_involutive
    right_inv := hodgeStar_involutive }

@[simp] theorem hodgeStarLinearEquiv_apply (x : Coord) :
    hodgeStarLinearEquiv x = hodgeStar x :=
  rfl

@[simp] theorem hodgeStarLinearEquiv_symm_apply (x : Coord) :
    hodgeStarLinearEquiv.symm x = hodgeStar x :=
  rfl

@[simp] theorem hodgeStarLinearEquiv_symm :
    hodgeStarLinearEquiv.symm = hodgeStarLinearEquiv := by
  apply LinearEquiv.ext
  intro x
  rfl

@[simp] theorem hodgeStarLinearEquiv_apply_apply (x : Coord) :
    hodgeStarLinearEquiv (hodgeStarLinearEquiv x) = x := by
  exact hodgeStar_involutive x

/-- The underlying linear map of the equivalence is exactly the original
coordinate Hodge-star owner. -/
theorem hodgeStarLinearEquiv_toLinearMap :
    hodgeStarLinearEquiv.toLinearMap = hodgeStar :=
  rfl

end InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
