import InfoGeometry.SuperMetriplectic.DrazinCartanShadowBridge
import InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# SuperMetriplectic Drazin Projector Constraint Bridge

Conservative bridge from the existing owner/operator lanes to the native
Drazin projector used for the topological-constraint carrier.

This file stays deliberately weaker than a full Drazin-Cartan identification:

* the topological constraint is exposed as the already-owned operator
  Drazin defect projector,
* the compact-lane statement is transported from the existing
  Drazin-Cartan compatibility packet,
* entropy vanishing is re-exported only on the existing owner central/BPS core.
-/

namespace InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge

open InfoGeometry.Krein
open InfoGeometry.SuperMetriplectic.DrazinCartanShadowBridge
open InfoGeometry.SuperMetriplectic.UnifiedOwnerTriadBridge

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
Compatibility packet aligning the owner Drazin-Cartan bridge with the native
operator Schur/Drazin closure on the same owner package.
-/
@[rep_depth transport]
structure DrazinProjectorConstraintCompatibility where
  drazinCartan : DrazinCartanCompatibility (E := E)
  triad : UnifiedOwnerTriadCompatibility (E := E)
  sameOwner : drazinCartan.owner = triad.owner

namespace DrazinProjectorConstraintCompatibility

variable (C : DrazinProjectorConstraintCompatibility (E := E))

/-! ## Native operator constraint projector -/

/-- The topological constraint projector on the actual Drazin operator carrier. -/
@[rep_depth operator]
noncomputable def topologicalConstraintProjector : EndH :=
  C.drazinCartan.cartan.spectralComplementaryProjector

@[rep_depth operator]
theorem topologicalConstraintProjector_idempotent :
    C.topologicalConstraintProjector *
        C.topologicalConstraintProjector =
      C.topologicalConstraintProjector := by
  simpa [topologicalConstraintProjector] using
    C.drazinCartan.cartan.spectralComplementaryProjector_idempotent

@[rep_depth operator]
theorem topologicalConstraintProjector_commutes_spectralGradingFlow
    (t : ℝ) :
    Commute C.topologicalConstraintProjector
      (C.drazinCartan.cartan.spectralGradingFlow t) := by
  simpa [topologicalConstraintProjector] using
    C.drazinCartan.cartan.spectralComplementaryProjector_commutes_spectralGradingFlow t

/--
The associated protected core lane is the existing owner central/BPS kernel.

No claim is made here that this is literally the image of a newly derived
operator projector; it is the core already owned by the odd-odd decomposition
packet attached to the shared owner.
-/
@[rep_depth transport]
noncomputable def topologicalConstraintCore : Submodule ℝ H₂ :=
  (ownerOddOddData C.triad.owner.U).centralBPSCore

@[rep_depth operator]
noncomputable def topologicalConstraintReadout : EndH :=
  C.topologicalConstraintProjector

@[rep_depth operator]
theorem topologicalConstraintReadout_eq_topologicalConstraintProjector :
    C.topologicalConstraintReadout = C.topologicalConstraintProjector := by
  rfl

@[rep_depth operator]
theorem operator_readout_seal :
    (C.topologicalConstraintReadout = C.topologicalConstraintProjector)
      ∧
    C.topologicalConstraintProjector * C.topologicalConstraintProjector =
      C.topologicalConstraintProjector := by
  exact ⟨C.topologicalConstraintReadout_eq_topologicalConstraintProjector,
    C.topologicalConstraintProjector_idempotent⟩

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
The native Drazin defect projector remains idempotent on the same carrier.
-/
@[rep_depth transport]
theorem drazinDefectProjector_idempotent :
    C.triad.block.drazinDefectProjector * C.triad.block.drazinDefectProjector =
      C.triad.block.drazinDefectProjector := by
  exact C.triad.block.drazinDefectProjector_idempotent

end DrazinProjectorConstraintCompatibility

end Core

end InfoGeometry.SuperMetriplectic.DrazinProjectorConstraintBridge
