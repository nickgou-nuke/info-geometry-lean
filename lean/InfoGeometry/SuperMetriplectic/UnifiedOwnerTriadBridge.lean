import InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge
import InfoGeometry.SuperMetriplectic.TriadBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Unified Owner Triad Bridge

Proof-carrying compatibility bridge between:

* the repo-owned operatorial Drazin odd-odd closure lane, and
* the existing scalar Schur/Drazin/body-entropy triad lane.

This file does not derive the scalar triad from the operator theory. It only
packages explicit scalar readouts of the operator owner channels and records
their agreement with the already-owned scalar Schur/Drazin/body surfaces.
-/

namespace UnifiedOwnerTriadBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.UnifiedOwnerClosureBridge
open InfoGeometry.SuperMetriplectic.TriadBridge

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
Compatibility packet between the operatorial owner closure and a scalar
Schur/Drazin/body-entropy triad.

The scalar maps `translationReadout` and `defectReadout` are explicit readout
choices from operator channels to body-level thermodynamic quantities.
-/
@[rep_depth transport]
structure UnifiedOwnerTriadCompatibility where
  owner : UnifiedDrazinSuperchargeClosureBridge (E := E)
  triad : InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad
  translationReadout : EndH → ℝ
  defectReadout : EndH → ℝ
  translation_matches_effectiveEvenOnsager :
    translationReadout
        (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate owner.U)
      = triad.block.effectiveEvenOnsager
  defect_matches_drazinDefectProjector :
    defectReadout owner.toSuperchargeClosure.defectShadow
      = triad.block.drazinDefectProjector

namespace UnifiedOwnerTriadCompatibility

variable (C : UnifiedOwnerTriadCompatibility (E := E))

/-- The operator translation lane reads out as the scalar effective even Onsager coefficient. -/
@[rep_depth transport]
theorem translationReadout_eq_effectiveEvenOnsager :
    C.translationReadout
        (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate C.owner.U)
      = C.triad.block.effectiveEvenOnsager :=
  C.translation_matches_effectiveEvenOnsager

/--
The carried defect readout matches the scalar Drazin defect projector through
the supermetriplectic closure bridge.
-/
@[rep_depth transport]
theorem defectReadout_eq_drazinDefectProjector :
    C.defectReadout C.owner.toSuperchargeClosure.defectShadow
      = C.triad.block.drazinDefectProjector :=
  C.defect_matches_drazinDefectProjector

/--
Since the residual defect vanishes on the owner slice, the same defect readout
can be taken directly on the owned central candidate.
-/
@[rep_depth transport]
theorem defectReadout_eq_ownerCentralCandidate :
    C.defectReadout
        (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate C.owner.U)
      = C.triad.block.drazinDefectProjector := by
  rw [← C.owner.toSuperchargeClosure_defectShadow_eq_ownerCentralCandidate]
  exact C.defectReadout_eq_drazinDefectProjector

/-- The scalar triad still carries its observable body-level second law. -/
@[rep_depth transport]
theorem body_entropy_nonnegative :
    0 ≤ C.triad.entropy.production :=
  InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad.body_entropy_nonnegative C.triad

/-- The scalar entropy packet still uses the scalar Schur complement as effective Onsager law. -/
@[rep_depth transport]
theorem effective_metric_is_schur_complement :
    C.triad.entropy.effectiveOnsager
      = C.triad.block.LPP
          - C.triad.block.LPΘ * C.triad.block.penrose.aPlus * C.triad.block.LΘP :=
  InfoGeometry.SuperMetriplectic.DrazinPenroseSchurTriad.effective_metric_is_schur_complement C.triad

/--
Combined capstone packet for the operator-to-body compatibility lane.
-/
@[capstone, rep_depth transport]
theorem ownerTriadCompatibility_packet :
    (C.translationReadout
        (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerTranslationCandidate C.owner.U)
      = C.triad.block.effectiveEvenOnsager)
      ∧
    (C.defectReadout
        (InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate C.owner.U)
      = C.triad.block.drazinDefectProjector)
      ∧
    (0 ≤ C.triad.entropy.production) := by
  refine ⟨C.translationReadout_eq_effectiveEvenOnsager, C.defectReadout_eq_ownerCentralCandidate, C.body_entropy_nonnegative⟩

end UnifiedOwnerTriadCompatibility

end Core

end UnifiedOwnerTriadBridge
