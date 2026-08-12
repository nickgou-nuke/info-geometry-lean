import InfoGeometry.Tessellation.Incidence
import InfoGeometry.Tessellation.NilpotentFlow
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge
import InfoGeometry.Canonical.TypeIIIModularCantorSystem
import InfoGeometry.Clifford.RealDoubledHestenesAnchor

/-!
# Tessellation Cantor Dirac-sea walk

Owner-side hopping packet over the repo's live Cantor boundary and binary-word
address lanes.

This file packages:
- infinite binary boundary codes;
- finite binary path addresses;
- sector idempotents at finite addresses;
- supported null hops between address sectors;
- charge admissibility for hops;
- a binary-word tilt readout.

This file does not yet construct:
- a stochastic/random-walk measure;
- a full super-Lie algebra of charges;
- a full Bogoliubov realization on the doubled Hestenes carrier;
- or an infinite CFT/VOA completion.
-/

namespace InfoGeometry.Tessellation

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBinaryTiltCARCCRBridge

/--
Owner-side Cantor/binary Dirac-sea walk datum.

The state-address lane uses the repo-owned finite and infinite binary-word
carriers. The hopping lane is modeled by supported incident lightrays between
the address sectors. Orthogonality is stored explicitly so square-zero and flow
transport follow by theorem from the tessellation owner lane.
-/
structure CantorDiracSeaWalkDatum
    (Op Charge : Type*) [Ring Op] where
  sector : List Bool → Diamond Op
  leftHop :
    ∀ w : List Bool,
      IncidentLightray Op (sector w)
        (sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false))
  rightHop :
    ∀ w : List Bool,
      IncidentLightray Op (sector w)
        (sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true))
  leftOrthogonal :
    ∀ w : List Bool,
      (sector w).P *
        (sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false)).P = 0
  rightOrthogonal :
    ∀ w : List Bool,
      (sector w).P *
        (sector (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true)).P = 0
  charge : List Bool → Charge
  admissibleLeft : List Bool → Prop
  admissibleRight : List Bool → Prop
  left_charge_respects :
    ∀ w : List Bool, admissibleLeft w
  right_charge_respects :
    ∀ w : List Bool, admissibleRight w
  tiltReadout : BinaryWordTiltReadout Op

namespace CantorDiracSeaWalkDatum

variable {Op Charge : Type*} [Ring Op]
variable (D : CantorDiracSeaWalkDatum Op Charge)

/-- The left binary hop is square-zero by orthogonal support. -/
theorem leftHop_square_zero
    (w : List Bool) :
    (D.leftHop w).N * (D.leftHop w).N = 0 :=
  (D.leftHop w).square_zero_of_orthogonal (D.leftOrthogonal w)

/-- The right binary hop is square-zero by orthogonal support. -/
theorem rightHop_square_zero
    (w : List Bool) :
    (D.rightHop w).N * (D.rightHop w).N = 0 :=
  (D.rightHop w).square_zero_of_orthogonal (D.rightOrthogonal w)

/-- The left binary hop generates a unipotent flow unit. -/
def leftFlowUnit
    (w : List Bool) : Opˣ :=
  (D.leftHop w).flowUnit (D.leftOrthogonal w)

/-- The right binary hop generates a unipotent flow unit. -/
def rightFlowUnit
    (w : List Bool) : Opˣ :=
  (D.rightHop w).flowUnit (D.rightOrthogonal w)

theorem leftFlowUnit_val
    (w : List Bool) :
    ((D.leftFlowUnit w : Opˣ) : Op) = 1 + (D.leftHop w).N := by
  simpa [leftFlowUnit, IncidentLightray.flowUnit] using
    (IncidentLightray.flowUnit_val
      (D.leftHop w) (D.leftOrthogonal w))

theorem rightFlowUnit_val
    (w : List Bool) :
    ((D.rightFlowUnit w : Opˣ) : Op) = 1 + (D.rightHop w).N := by
  simpa [rightFlowUnit, IncidentLightray.flowUnit] using
    (IncidentLightray.flowUnit_val
      (D.rightHop w) (D.rightOrthogonal w))

theorem leftFlowUnit_inv_val
    (w : List Bool) :
    (((D.leftFlowUnit w)⁻¹ : Opˣ) : Op) = 1 - (D.leftHop w).N := by
  simpa [leftFlowUnit, IncidentLightray.flowUnit] using
    (oneAddSquareZeroUnit_inv_val
      (D.leftHop w).N (D.leftHop_square_zero w))

theorem rightFlowUnit_inv_val
    (w : List Bool) :
    (((D.rightFlowUnit w)⁻¹ : Opˣ) : Op) = 1 - (D.rightHop w).N := by
  simpa [rightFlowUnit, IncidentLightray.flowUnit] using
    (oneAddSquareZeroUnit_inv_val
      (D.rightHop w).N (D.rightHop_square_zero w))

/-- Prepending a false bit exposes `false` as the new boundary head. -/
@[simp] theorem boundaryHead_boundaryCons_false
    (ξ : (ℕ → Bool)) :
    boundaryHead (boundaryCons false ξ) = false := by
  simp

/-- Prepending a true bit exposes `true` as the new boundary head. -/
@[simp] theorem boundaryHead_boundaryCons_true
    (ξ : (ℕ → Bool)) :
    boundaryHead (boundaryCons true ξ) = true := by
  simp

/-- The first prefix symbol of a false-prepended boundary code is `false`. -/
theorem boundaryPrefix_one_false
    (ξ : (ℕ → Bool)) :
    boundaryPrefix 1 (boundaryCons false ξ) = [false] := by
  simp [boundaryPrefix]

/-- The first prefix symbol of a true-prepended boundary code is `true`. -/
theorem boundaryPrefix_one_true
    (ξ : (ℕ → Bool)) :
    boundaryPrefix 1 (boundaryCons true ξ) = [true] := by
  simp [boundaryPrefix]

end CantorDiracSeaWalkDatum

end InfoGeometry.Tessellation
