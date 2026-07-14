import InfoGeometry.Tessellation.CantorDiracSeaCharge
import InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

/-!
# InfoGeometry.Clifford.CantorDiracSeaChargeHestenesBridge

Thin compatibility bridge between the Cantor/binary charge packet and the
doubled real Hestenes carrier bridge.

This file does not construct a charge readout from doubled-carrier operators.
Instead it stores only the primitive compatibility laws saying that a chosen
doubled-carrier charge readout transforms under realized left/right hops by
the same `flipBit` laws as the owner-side Cantor Dirac-sea charge packet.
-/

open scoped InnerProductSpace

noncomputable section

namespace CantorDiracSeaChargeHestenesBridge

open InfoGeometry.Tessellation
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.CondensedMatter.CliffordAtomsZ2n
open InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Compatibility packet between the owner-side Cantor charge datum and a doubled
carrier realization of the same walk.

The crucial primitive laws are that the charge readout on the doubled carrier
obeys the same left/right `flipBit` transformation laws as the finite-address
owner-side charge packet.
-/
@[rep_depth krein]
structure CantorDiracSeaChargeHestenesPacket
    (Op : Type*) [Ring Op] where
  chargeDatum : Tessellation.CantorDiracSeaChargeDatum Op
  hestenes : CantorDiracSeaHestenesPacket (E := E) Op (Z2Charge Bool)
  walk_eq : hestenes.walk = chargeDatum.walk
  chargeReadout : H₂ → Z2Charge Bool
  left_realized_charge_law :
    ∀ (w : FiniteBinaryWord) (ξ : H₂),
      chargeReadout (hestenes.realizeLeftHop w ξ) =
        flipBit false (chargeReadout ξ)
  right_realized_charge_law :
    ∀ (w : FiniteBinaryWord) (ξ : H₂),
      chargeReadout (hestenes.realizeRightHop w ξ) =
        flipBit true (chargeReadout ξ)

namespace CantorDiracSeaChargeHestenesPacket

variable {Op : Type*} [Ring Op]
variable (P : CantorDiracSeaChargeHestenesPacket (E := E) Op)

/-- The doubled-carrier left hop flips the false-bit charge coordinate. -/
@[rep_depth krein]
theorem left_realized_flips_false_bit
    (w : FiniteBinaryWord) (ξ : H₂) :
    P.chargeReadout (P.hestenes.realizeLeftHop w ξ) false =
      !(P.chargeReadout ξ false) := by
  rw [P.left_realized_charge_law]
  simp

/-- The doubled-carrier left hop preserves the true-bit charge coordinate. -/
@[rep_depth krein]
theorem left_realized_preserves_true_bit
    (w : FiniteBinaryWord) (ξ : H₂) :
    P.chargeReadout (P.hestenes.realizeLeftHop w ξ) true =
      P.chargeReadout ξ true := by
  rw [P.left_realized_charge_law]
  simp

/-- The doubled-carrier right hop flips the true-bit charge coordinate. -/
@[rep_depth krein]
theorem right_realized_flips_true_bit
    (w : FiniteBinaryWord) (ξ : H₂) :
    P.chargeReadout (P.hestenes.realizeRightHop w ξ) true =
      !(P.chargeReadout ξ true) := by
  rw [P.right_realized_charge_law]
  simp

/-- The doubled-carrier right hop preserves the false-bit charge coordinate. -/
@[rep_depth krein]
theorem right_realized_preserves_false_bit
    (w : FiniteBinaryWord) (ξ : H₂) :
    P.chargeReadout (P.hestenes.realizeRightHop w ξ) false =
      P.chargeReadout ξ false := by
  rw [P.right_realized_charge_law]
  simp

/-- Owner-side left charge law readback through the shared walk datum. -/
@[rep_depth operator]
theorem owner_left_charge
    (w : FiniteBinaryWord) :
    P.hestenes.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w false) =
      flipBit false (P.hestenes.walk.charge w) := by
  rw [P.walk_eq]
  exact P.chargeDatum.left_charge_law w

/-- Owner-side right charge law readback through the shared walk datum. -/
@[rep_depth operator]
theorem owner_right_charge
    (w : FiniteBinaryWord) :
    P.hestenes.walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.BinaryWord.child w true) =
      flipBit true (P.hestenes.walk.charge w) := by
  rw [P.walk_eq]
  exact P.chargeDatum.right_charge_law w

end CantorDiracSeaChargeHestenesPacket

end CantorDiracSeaChargeHestenesBridge
