import InfoGeometry.SuperMetriplectic.DrazinCartanShadowBridge
import InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Drazin Projector Constraint Bridge

Conservative bridge from the existing owner/operator lanes to the scalar
Drazin-projector readout used as a topological-constraint shadow.

This file stays deliberately weaker than a full Drazin-Cartan identification:

* the topological constraint is exposed only as the already-owned scalar
  Drazin defect projector,
* the compact-lane statement is transported from the existing
  Drazin-Cartan compatibility packet,
* entropy vanishing is re-exported only on the existing owner central/BPS core.
-/

namespace DrazinProjectorConstraintBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.DrazinCartanShadowBridge
open InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge
open InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge

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

local notation "ownerCentral" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.ownerCentralCandidate
local notation "ownerOddOddData" =>
  InfoGeometry.Canonical.UnifiedSuperchargeOddOddBridge.UnifiedSuperchargePackage.toOddOddDecompositionData

/--
Compatibility packet aligning:

* the owner Drazin-Cartan shadow bridge, and
* the owner-to-scalar Drazin/Schur/body-entropy bridge

on the same underlying owner supercharge package.
-/
@[rep_depth transport]
structure DrazinProjectorConstraintCompatibility where
  drazinCartan : DrazinCartanCompatibility (E := E)
  triad : UnifiedOwnerTriadCompatibility (E := E)
  sameOwner : drazinCartan.owner = triad.owner

namespace DrazinProjectorConstraintCompatibility

variable (C : DrazinProjectorConstraintCompatibility (E := E))

/--
Scalar Drazin-projector readout used as the topological constraint shadow.

This is intentionally a readout surface, not an operator-level projector
identification theorem.
-/
@[rep_depth transport]
noncomputable def topologicalConstraintProjector : ℝ :=
  C.triad.triad.block.drazinDefectProjector

/--
The associated protected core lane is the existing owner central/BPS kernel.

No claim is made here that this is literally the image of a newly derived
operator projector; it is the core already owned by the odd-odd decomposition
packet attached to the shared owner.
-/
@[rep_depth transport]
noncomputable def topologicalConstraintCore : Submodule ℝ H₂ :=
  (ownerOddOddData C.triad.owner.U).centralBPSCore

/-- Public scalar formula for the Drazin-projector readout. -/
@[rep_depth transport]
theorem topologicalConstraintProjector_eq_drazin_formula :
    C.topologicalConstraintProjector
      = 1 - C.triad.triad.block.LΘΘ * C.triad.triad.block.drazin.aD := by
  exact InfoGeometry.SuperMetriplectic.ScalarSchurDrazinBlock.drazinDefectProjector_eq
    C.triad.triad.block

/-- Readout-first alias for the scalar topological-constraint projector lane. -/
@[rep_depth transport]
noncomputable def topologicalConstraintReadout : ℝ :=
  C.topologicalConstraintProjector

/-- The readout alias is definitionally the scalar topological-constraint projector. -/
@[rep_depth transport]
theorem topologicalConstraintReadout_eq_topologicalConstraintProjector :
    C.topologicalConstraintReadout = C.topologicalConstraintProjector := by
  rfl

/-- Readout-first restatement of the scalar Drazin-projector formula. -/
@[rep_depth transport]
theorem topologicalConstraintProjector_readout_eq_drazin_formula :
    C.topologicalConstraintReadout
      = 1 - C.triad.triad.block.LΘΘ * C.triad.triad.block.drazin.aD := by
  simpa [topologicalConstraintReadout] using C.topologicalConstraintProjector_eq_drazin_formula

/--
The scalar defect readout of the owner central channel is exactly the
 topological-constraint projector shadow.
-/
@[rep_depth transport]
theorem defectReadout_eq_topologicalConstraintProjector :
    C.triad.defectReadout (ownerCentral C.triad.owner.U)
      = C.topologicalConstraintProjector := by
  exact C.triad.defectReadout_eq_ownerCentralCandidate

/--
Readout-seal theorem for the scalar topological-constraint lane.

This records that the exported scalar readout is tied to the carried Drazin
projector shadow; it does not replace noncommuting operator dynamics.
-/
@[rep_depth transport]
theorem scalar_readout_seal :
    (C.topologicalConstraintReadout = C.topologicalConstraintProjector)
      ∧
    (C.topologicalConstraintReadout
      = 1 - C.triad.triad.block.LΘΘ * C.triad.triad.block.drazin.aD) := by
  exact ⟨C.topologicalConstraintReadout_eq_topologicalConstraintProjector,
    C.topologicalConstraintProjector_readout_eq_drazin_formula⟩

/--
The shared owner central lane lies in the compact Cartan sector `𝔨`.

This is transported from the existing Drazin-Cartan compatibility packet.
-/
@[rep_depth transport]
theorem ownerCentralCandidate_in_cartan_k :
    ownerCentral C.triad.owner.U ∈ (C.drazinCartan.cartan.toCartanOnsagerSplit).S.𝔨 := by
  have h :=
    C.drazinCartan.ownerCentralCandidate_in_cartan_k
  simpa [C.sameOwner] using h

/--
Entropy production vanishes on the protected owner central/BPS core associated
to the topological-constraint lane.
-/
@[rep_depth transport]
theorem entropyProduction_vanishes_on_topologicalConstraintCore
    (ψ : H₂) (hψ : ψ ∈ C.topologicalConstraintCore) :
    InfoGeometry.Canonical.SuperchargeOddOddDecomposition.entropyProductionShadow
      (ownerCentral C.triad.owner.U) ψ = 0 := by
  exact C.triad.owner.entropyProduction_vanishes_on_ownerCentralCore ψ hψ

/--
The scalar body-entropy packet carried by the same triad remains nonnegative.
-/
@[rep_depth transport]
theorem totalEntropyChange_nonnegative :
    0 ≤
      (InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge.UnifiedOwnerTriadCompatibility.toCoadjointLeafEntropySplit
        C.triad).totalEntropyChange := by
  exact
    InfoGeometry.SuperMetriplectic.UnifiedOwnerEntropyBridge.UnifiedOwnerTriadCompatibility.toCoadjointLeafEntropySplit_totalEntropyChange_nonnegative
      C.triad

end DrazinProjectorConstraintCompatibility

end Core

end DrazinProjectorConstraintBridge
