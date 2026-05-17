import InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Canonical.PrimeExteriorMobiusCalibration

Canonical bridge re-export for the finite exterior Möbius parity readout.

This wrapper adds no arithmetic content. It makes the finite bridge surface
owner-facing and bridge-tagged.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeExteriorMobiusCalibration

/-- Canonical bridge re-export of the finite exterior Möbius/chirality theorem. -/
@[bridge_target_tag]
theorem canonicalMobius_stateNat_eq_Gamma
    {P : InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.PrimeCutoff}
    (S : InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.SquareFreeState P) :
    ArithmeticFunction.moebius
        (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.stateNat S) =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S := by
  bridge
    (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.mobius_stateNat_eq_Gamma
      (S := S))

/-- Canonical owner target for the finite exterior Möbius bridge. -/
@[owner_target_tag]
def PrimeExteriorMobiusCalibrationOwnerTarget : Prop :=
  ∀ {P : InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.PrimeCutoff}
    (S : InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.SquareFreeState P),
    ArithmeticFunction.moebius
        (InfoGeometry.Arithmetic.PrimeExteriorMobiusBridge.stateNat S) =
      InfoGeometry.Arithmetic.PrimeExteriorRepresentation.SquareFreePrimeState.Gamma S

/-- The canonical exterior Möbius owner target is proved. -/
theorem primeExteriorMobiusCalibrationOwnerTarget :
    PrimeExteriorMobiusCalibrationOwnerTarget := by
  intro P S
  exact canonicalMobius_stateNat_eq_Gamma S

end InfoGeometry.Canonical.PrimeExteriorMobiusCalibration
