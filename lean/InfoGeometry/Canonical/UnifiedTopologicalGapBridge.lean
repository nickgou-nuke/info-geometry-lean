import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.TopologicalGapShadow
import InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge
import Mathlib

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.UnifiedTopologicalGapBridge

Proof-carrying bridge from the repo-owned unified Drazin supercharge lane to the
generic topological-gap shadow interface.

This file exports the repo-owned unified Drazin odd-odd lane into the generic
topological-gap shadow interface.

* `TopologicalGapShadow` owns the gap/core/excited-sector API,
* `UnifiedSuperchargeOddOddBridge` owns the derived odd-odd decomposition.

Because the gap owner now uses the same real odd-odd self-closure `{Q_D, Q_D}`
as the unified Drazin lane, no extra compatibility hypothesis is needed here.
-/

namespace InfoGeometry.Canonical.UnifiedTopologicalGapBridge

open InfoGeometry.Krein
open InfoGeometry.Canonical.TopologicalGapShadow
open InfoGeometry.Canonical.SuperchargeHoppingBridge
open InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge

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

/-- Bridge packet tying the unified Drazin owner lane to the generic gap
shadow on the same carrier. -/
@[rep_depth transport]
structure UnifiedTopologicalGapCompatibility where
  U : InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage (E := E)

namespace UnifiedTopologicalGapCompatibility

variable (C : UnifiedTopologicalGapCompatibility (E := E))
local notation "ownerTranslation" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate
local notation "ownerCentral" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate
local notation "ownerResidual" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerDefectResidual

/-- The owner BPS/Drazin core read through the generic topological-gap owner. -/
@[rep_depth transport]
noncomputable def ownerDrazinCore : Submodule ℝ H₂ :=
  InfoGeometry.Canonical.TopologicalGapShadow.DrazinCore
    (Q := InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)

/-- The owner excited sector read through the generic topological-gap owner. -/
@[rep_depth transport]
noncomputable def ownerExcitedStateSector : Submodule ℝ H₂ :=
  InfoGeometry.Canonical.TopologicalGapShadow.ExcitedStateSector
    (Q := InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)

/--
The unified Drazin supercharge induces the same hopping/gap operator as the
repo-owned odd-odd closure by the repo-native self-bracket identity.
-/
@[rep_depth transport]
theorem susyHoppingOperator_QD_eq_ownerOddOdd :
    susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
      =
    oddOddBracket
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U) :=
  InfoGeometry.Canonical.SuperchargeHoppingBridge.susyHoppingOperator_eq_oddOddBracket_self
    (Q := InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)

/--
On the owner slice, the gap operator decomposes into translation, central, and
residual defect lanes.
-/
@[rep_depth transport]
theorem susyHoppingOperator_QD_eq_translation_plus_central_plus_defectResidual :
    susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
      =
    ownerTranslation C.U
      + ownerCentral C.U
      + ownerResidual C.U := by
  rw [C.susyHoppingOperator_QD_eq_ownerOddOdd]
  exact
    InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.oddOddBracket_eq_translation_plus_central_plus_defectResidual
      (U := C.U)

/--
Because the residual defect vanishes on the owner slice, the same gap operator
reduces to translation plus the protected central lane.
-/
@[capstone, rep_depth transport]
theorem susyHoppingOperator_QD_eq_translation_plus_central :
    susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
      =
    ownerTranslation C.U
      + ownerCentral C.U := by
  calc
    susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
        =
      ownerTranslation C.U
        + ownerCentral C.U
        + ownerResidual C.U := by
          exact C.susyHoppingOperator_QD_eq_translation_plus_central_plus_defectResidual
    _ =
      ownerTranslation C.U
        + ownerCentral C.U := by
          rw [InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerDefectResidual_eq_zero (U := C.U)]
          simp

/--
Entropy-production readout vanishes on the owner Drazin core through the
generic topological-gap shadow interface.
-/
@[rep_depth transport]
theorem entropyProduction_vanishes_on_ownerDrazinCore
    (ψ : H₂) (h_core : ψ ∈ C.ownerDrazinCore) :
    ‖(susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)) ψ‖ = 0 := by
  exact
    InfoGeometry.Canonical.TopologicalGapShadow.entropy_production_vanishes_on_core
      (Q := InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U) ψ h_core

/--
If a proof-carrying gap datum is supplied on the owner Drazin lane, its lower
bound acts exactly on the owner excited-state sector.
-/
@[rep_depth transport]
theorem gapDatum_bound_on_ownerExcitedSector
    (gap : InfoGeometry.Canonical.TopologicalGapShadow.GapDatum
      (Q := InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U))
    (ψ : H₂) (h_excited : ψ ∈ C.ownerExcitedStateSector) :
    ‖(susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)) ψ‖
      ≥ gap.Δ * ‖ψ‖ := by
  exact gap.bound ψ h_excited

/--
Combined owner packet for the unified-gap bridge.
-/
@[capstone, rep_depth transport]
theorem unified_topological_gap_packet :
    (susyHoppingOperator
        (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)
      =
    ownerTranslation C.U
      + ownerCentral C.U)
      ∧
    (∀ ψ : H₂, ψ ∈ C.ownerDrazinCore →
      ‖(susyHoppingOperator
          (InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD C.U)) ψ‖ = 0) := by
  refine ⟨C.susyHoppingOperator_QD_eq_translation_plus_central, ?_⟩
  intro ψ hψ
  exact C.entropyProduction_vanishes_on_ownerDrazinCore ψ hψ

end UnifiedTopologicalGapCompatibility

end Core

end InfoGeometry.Canonical.UnifiedTopologicalGapBridge
