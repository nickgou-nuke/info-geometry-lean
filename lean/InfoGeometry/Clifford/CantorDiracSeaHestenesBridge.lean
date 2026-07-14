import InfoGeometry.Tessellation.CantorDiracSeaWalk
import InfoGeometry.Clifford.RealDoubledHestenesAnchor
import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

Thin compatibility bridge between the owner-side Cantor/binary Dirac-sea walk
packet and the doubled real Hestenes/Krein carrier.

This file does not construct a concrete Bogoliubov action from the walk data.
Instead it stores the smallest theorem-level compatibility fields needed to say
that the walk's tilt/hop operators are represented on the doubled real carrier.

What is stored here:
- a Cantor/binary walk datum;
- a rotor family on the doubled real carrier;
- an abstract operator realization of left/right hops and the tilt readout;
- explicit preservation laws for the doubled phase axis and doubled Krein null cone.

What is not claimed here:
- a stochastic/random-walk measure;
- a full super-Lie closure theorem for the charges;
- a concrete Bogoliubov constructor from the walk datum alone;
- or an infinite VOA/CFT completion.
-/

open scoped InnerProductSpace

noncomputable section

namespace CantorDiracSeaHestenesBridge

open InfoGeometry.Tessellation
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Krein

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Compatibility packet between the Cantor Dirac-sea walk datum and the doubled
real Hestenes/Krein carrier.

The bridge is theorem-safe: it stores only the compatibility data actually
needed downstream, without claiming that the walk datum canonically constructs
these operators.
-/
@[rep_depth krein]
structure CantorDiracSeaHestenesPacket
    (Op Charge : Type*) [Ring Op] where
  walk : Tessellation.CantorDiracSeaWalkDatum Op Charge
  /-- Real rotor acting on the doubled carrier. -/
  rotor : ℝ → H₂ →L[ℝ] H₂
  /-- Inverse rotor acting on the doubled carrier. -/
  rotorInv : ℝ → H₂ →L[ℝ] H₂
  /-- Realization of left hops on the doubled carrier. -/
  realizeLeftHop :
    FiniteBinaryWord → H₂ →L[ℝ] H₂
  /-- Realization of right hops on the doubled carrier. -/
  realizeRightHop :
    FiniteBinaryWord → H₂ →L[ℝ] H₂
  /-- Realization of the binary tilt readout on the doubled carrier. -/
  realizeBitOperator :
    Bool → H₂ →L[ℝ] H₂
  /-- Rotor conjugation preserves the doubled phase axis. -/
  rotor_preserves_phaseAxis :
    ∀ t : ℝ,
      rotor t ∘L InfoGeometry.Krein.doubledI (E := E) =
        InfoGeometry.Krein.doubledI (E := E) ∘L rotor t
  /-- The rotor preserves the doubled-carrier inner product. -/
  rotor_preserves_doubledInner :
    ∀ (t : ℝ) (ξ η : H₂),
      ⟪rotor t ξ, rotor t η⟫_ℝ = ⟪ξ, η⟫_ℝ
  /-- The realized left hop matches the stored square-zero owner law. -/
  realizeLeftHop_square_zero :
    ∀ w : FiniteBinaryWord,
      realizeLeftHop w ∘L realizeLeftHop w = 0
  /-- The realized right hop matches the stored square-zero owner law. -/
  realizeRightHop_square_zero :
    ∀ w : FiniteBinaryWord,
      realizeRightHop w ∘L realizeRightHop w = 0

namespace CantorDiracSeaHestenesPacket

variable {Op Charge : Type*} [Ring Op]
variable (P : CantorDiracSeaHestenesPacket (E := E) Op Charge)

/-- Readback of the doubled phase-axis square law. -/
@[rep_depth krein]
theorem phaseAxis_sq :
    InfoGeometry.Krein.doubledI (E := E) * InfoGeometry.Krein.doubledI (E := E) =
      -(1 : H₂ →L[ℝ] H₂) :=
  InfoGeometry.Krein.doubledI_sq (E := E)

/-- Rotor action preserves the doubled phase axis. -/
@[rep_depth krein]
theorem rotor_commutes_phaseAxis (t : ℝ) :
    P.rotor t ∘L InfoGeometry.Krein.doubledI (E := E) =
      InfoGeometry.Krein.doubledI (E := E) ∘L P.rotor t :=
  P.rotor_preserves_phaseAxis t

/-- The rotor preserves null vectors on the doubled carrier. -/
@[rep_depth krein]
theorem rotor_preserves_null_cone
    (t : ℝ) {ξ : H₂}
    (h_null : ⟪ξ, ξ⟫_ℝ = 0) :
    ⟪P.rotor t ξ, P.rotor t ξ⟫_ℝ = 0 := by
  rw [P.rotor_preserves_doubledInner t ξ ξ]
  exact h_null

/-- Readback of the realized left-hop square-zero law. -/
@[rep_depth krein]
theorem leftHop_realization_square_zero (w : FiniteBinaryWord) :
    P.realizeLeftHop w ∘L P.realizeLeftHop w = 0 :=
  P.realizeLeftHop_square_zero w

/-- Readback of the realized right-hop square-zero law. -/
@[rep_depth krein]
theorem rightHop_realization_square_zero (w : FiniteBinaryWord) :
    P.realizeRightHop w ∘L P.realizeRightHop w = 0 :=
  P.realizeRightHop_square_zero w

/-- The walk's left hop is square-zero in the owner lane. -/
@[rep_depth operator]
theorem owner_leftHop_square_zero (w : FiniteBinaryWord) :
    (P.walk.leftHop w).N * (P.walk.leftHop w).N = 0 :=
  P.walk.leftHop_square_zero w

/-- The walk's right hop is square-zero in the owner lane. -/
@[rep_depth operator]
theorem owner_rightHop_square_zero (w : FiniteBinaryWord) :
    (P.walk.rightHop w).N * (P.walk.rightHop w).N = 0 :=
  P.walk.rightHop_square_zero w

/-- Readback of the Hestenes doubled-bivector theorem available for this carrier. -/
@[rep_depth krein]
theorem doubledIBivector_square_neg :
    (InfoGeometry.Clifford.RealDoubledHestenesAnchor.doubledIBivector (E := E)).square_neg =
      InfoGeometry.Krein.doubledI_sq (E := E) := by
  rfl

end CantorDiracSeaHestenesPacket

end CantorDiracSeaHestenesBridge
