import InfoGeometry.Tessellation.CantorDiracSeaCharge
import InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Clifford.CantorDiracSeaChargeHestenesBridge

open InfoGeometry.Tessellation
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.CondensedMatter.CliffordAtomsZ2n
open InfoGeometry.Canonical.TypeIIIModularCantorSystem
open InfoGeometry.Clifford.CantorDiracSeaHestenesBridge

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

theorem left_realized_flips_false_bit
    {Op : Type*} [Ring Op]
    (realizeLeftHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (chargeReadout : H₂ → Z2Charge Bool)
    (left_charge_law :
      ∀ (w : FiniteBinaryWord) (ξ : H₂),
        chargeReadout (realizeLeftHop w ξ) =
          flipBit false (chargeReadout ξ))
    (w : FiniteBinaryWord) (ξ : H₂) :
    chargeReadout (realizeLeftHop w ξ) false =
      !(chargeReadout ξ false) := by
  rw [left_charge_law]
  simp

theorem left_realized_preserves_true_bit
    {Op : Type*} [Ring Op]
    (realizeLeftHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (chargeReadout : H₂ → Z2Charge Bool)
    (left_charge_law :
      ∀ (w : FiniteBinaryWord) (ξ : H₂),
        chargeReadout (realizeLeftHop w ξ) =
          flipBit false (chargeReadout ξ))
    (w : FiniteBinaryWord) (ξ : H₂) :
    chargeReadout (realizeLeftHop w ξ) true =
      chargeReadout ξ true := by
  rw [left_charge_law]
  simp

theorem right_realized_flips_true_bit
    {Op : Type*} [Ring Op]
    (realizeRightHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (chargeReadout : H₂ → Z2Charge Bool)
    (right_charge_law :
      ∀ (w : FiniteBinaryWord) (ξ : H₂),
        chargeReadout (realizeRightHop w ξ) =
          flipBit true (chargeReadout ξ))
    (w : FiniteBinaryWord) (ξ : H₂) :
    chargeReadout (realizeRightHop w ξ) true =
      !(chargeReadout ξ true) := by
  rw [right_charge_law]
  simp

theorem right_realized_preserves_false_bit
    {Op : Type*} [Ring Op]
    (realizeRightHop : FiniteBinaryWord → H₂ →L[ℝ] H₂)
    (chargeReadout : H₂ → Z2Charge Bool)
    (right_charge_law :
      ∀ (w : FiniteBinaryWord) (ξ : H₂),
        chargeReadout (realizeRightHop w ξ) =
          flipBit true (chargeReadout ξ))
    (w : FiniteBinaryWord) (ξ : H₂) :
    chargeReadout (realizeRightHop w ξ) false =
      chargeReadout ξ false := by
  rw [right_charge_law]
  simp

theorem owner_left_charge
    {Op : Type*} [Ring Op]
    (chargeDatum : Tessellation.CantorDiracSeaChargeDatum Op)
    (walk : Tessellation.CantorDiracSeaWalkDatum Op (Z2Charge Bool))
    (walk_eq : walk = chargeDatum.walk)
    (w : List Bool) :
    walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w false) =
      flipBit false (walk.charge w) := by
  rw [walk_eq]
  exact chargeDatum.left_charge_law w

theorem owner_right_charge
    {Op : Type*} [Ring Op]
    (chargeDatum : Tessellation.CantorDiracSeaChargeDatum Op)
    (walk : Tessellation.CantorDiracSeaWalkDatum Op (Z2Charge Bool))
    (walk_eq : walk = chargeDatum.walk)
    (w : List Bool) :
    walk.charge
        (InfoGeometry.Canonical.TypeIIIModularCantorSystem.child w true) =
      flipBit true (walk.charge w) := by
  rw [walk_eq]
  exact chargeDatum.right_charge_law w

end InfoGeometry.Clifford.CantorDiracSeaChargeHestenesBridge
