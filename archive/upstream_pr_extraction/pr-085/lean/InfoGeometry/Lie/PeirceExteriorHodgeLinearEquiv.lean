import InfoGeometry.Canonical.SplitOctonionCayleyHodgeLinearEquiv
import InfoGeometry.Lie.PeirceExteriorHodgeTransport

/-!
# Native Hodge equivalence on the Peirce carrier

The existing `peirceHodgeStar` is the conjugate of the explicit coordinate
Hodge star by `peirceExterior3Equiv`.  This file packages the same transport as
Mathlib's native `LinearEquiv` and proves that its underlying linear map is the
existing owner.
-/

noncomputable section

namespace InfoGeometry.Lie.PeirceExteriorHodgeTransport

open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge
open InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge

/-- The coordinate Hodge equivalence transported to the Peirce carrier. -/
noncomputable def peirceHodgeStarLinearEquiv :
    PeirceCarrier ≃ₗ[ℝ] PeirceCarrier :=
  peirceExterior3Equiv.symm.trans
    (hodgeStarLinearEquiv.trans peirceExterior3Equiv)

@[simp] theorem peirceHodgeStarLinearEquiv_apply
    (x : PeirceCarrier) :
    peirceHodgeStarLinearEquiv x = peirceHodgeStar x := by
  rw [peirceHodgeStar_apply_all]
  rfl

/-- The transported equivalence introduces no second Hodge operator: its
underlying linear map is exactly the existing `peirceHodgeStar`. -/
theorem peirceHodgeStarLinearEquiv_toLinearMap :
    peirceHodgeStarLinearEquiv.toLinearMap = peirceHodgeStar := by
  apply LinearMap.ext
  intro x
  exact peirceHodgeStarLinearEquiv_apply x

@[simp] theorem peirceHodgeStarLinearEquiv_apply_apply
    (x : PeirceCarrier) :
    peirceHodgeStarLinearEquiv (peirceHodgeStarLinearEquiv x) = x := by
  rw [peirceHodgeStarLinearEquiv_apply,
    peirceHodgeStarLinearEquiv_apply]
  have h := LinearMap.congr_fun peirceHodgeStar_sq x
  simpa [Module.End.mul_eq_comp] using h

end InfoGeometry.Lie.PeirceExteriorHodgeTransport
