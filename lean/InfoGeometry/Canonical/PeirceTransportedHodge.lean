import InfoGeometry.Canonical.TransportedInvolution
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitOctonionCayleyHodgeLinearEquiv
import InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

/-!
# Hodge transport to the native Peirce carrier

The coordinate Hodge map is transported through the established linear
equivalence rather than being redefined on the Zorn/Peirce carrier.
-/

namespace InfoGeometry.Canonical.PeirceTransportedHodge

open InfoGeometry.Canonical.TransportedInvolution
open InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge
open InfoGeometry.Lie.SplitOctonionPeirceExterior3CoordinateBridge

abbrev Coord := Exterior3Coordinates
abbrev Carrier := PeirceCarrier

noncomputable def hodgeStar : Carrier →ₗ[ℝ] Carrier :=
  transport peirceExterior3Equiv hodgeStarLinearEquiv.toLinearMap

noncomputable def gradedChirality : Carrier →ₗ[ℝ] Carrier :=
  transport peirceExterior3Equiv
    InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge.gradedChirality

@[simp] theorem hodgeStar_apply (x : Carrier) :
    hodgeStar x = peirceExterior3Equiv
      (hodgeStarLinearEquiv (peirceExterior3Equiv.symm x)) := rfl

theorem hodgeStar_involutive :
    hodgeStar.comp hodgeStar = LinearMap.id := by
  apply transport_involutive peirceExterior3Equiv
  simpa [hodgeStarLinearEquiv] using hodgeStar_sq

theorem gradedChirality_involutive :
    gradedChirality.comp gradedChirality = LinearMap.id := by
  apply transport_involutive peirceExterior3Equiv
  simpa using
    InfoGeometry.Canonical.SplitOctonionCayleyHodgeDualityBridge.gradedChirality_sq

end InfoGeometry.Canonical.PeirceTransportedHodge
