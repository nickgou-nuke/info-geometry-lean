import InfoGeometry.SuperMetriplectic.CartanBridge
import InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Drazin-Cartan Shadow Bridge

Proof-carrying compatibility packet between:

* the operatorial Drazin odd-odd owner closure lane, and
* the existing Cartan `𝔨 ⊕ 𝔭` split on the same operator carrier.

This is intentionally a shadow bridge, not a full isomorphism theorem.
The Cartan split is already owned by `CartanBridge`; this file only packages
the additional compatibility data saying which owner channels land in which
Cartan sectors.
-/

namespace DrazinCartanShadowBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.CartanBridge
open InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Compatibility packet aligning the owner Drazin closure lanes with the Cartan
`𝔨 ⊕ 𝔭` split on the same operator carrier.
-/
@[rep_depth transport]
structure DrazinCartanCompatibility where
  owner : UnifiedDrazinSuperchargeClosureBridge (E := E)
  cartan : DrazinCartanOnsagerBridge (E := H₂)
  central_in_drazinCore :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate owner.U
      ∈ (cartan.toCartanOnsagerSplit).drazinCore
  translation_in_cartan_p :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate owner.U
      ∈ (cartan.toCartanOnsagerSplit).S.𝔭

namespace DrazinCartanCompatibility

variable (C : DrazinCartanCompatibility (E := E))

/--
Proof-carrying compact-lane theorem: the owner central candidate lies in the
Cartan compact sector whenever the compatibility packet places it in the
Drazin/core side of the split.
-/
@[rep_depth transport]
theorem ownerCentralCandidate_in_cartan_k_of_drazinCore :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate C.owner.U
      ∈ (C.cartan.toCartanOnsagerSplit).S.𝔨 := by
  rw [← C.cartan.toCartanOnsagerSplit_drazinCore_eq_k]
  exact C.central_in_drazinCore

/-- The carried central lane lies in the compact/Drazin Cartan sector `𝔨`. -/
@[rep_depth transport]
theorem ownerCentralCandidate_in_cartan_k :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate C.owner.U
      ∈ (C.cartan.toCartanOnsagerSplit).S.𝔨 := by
  exact C.ownerCentralCandidate_in_cartan_k_of_drazinCore

/-- The carried translation lane lies in the dissipative Cartan sector `𝔭`. -/
@[rep_depth transport]
theorem ownerTranslationCandidate_in_cartan_p :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate C.owner.U
      ∈ (C.cartan.toCartanOnsagerSplit).S.𝔭 := by
  exact C.translation_in_cartan_p

/-- The carried translation lane lives in the dissipative range of the split. -/
@[rep_depth transport]
theorem ownerTranslationCandidate_in_dissipativeRange :
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate C.owner.U
      ∈ (C.cartan.toCartanOnsagerSplit).dissipativeRange := by
  simpa [C.cartan.toCartanOnsagerSplit_dissipativeRange_eq_p] using
    C.ownerTranslationCandidate_in_cartan_p

end DrazinCartanCompatibility

end Core

end DrazinCartanShadowBridge
