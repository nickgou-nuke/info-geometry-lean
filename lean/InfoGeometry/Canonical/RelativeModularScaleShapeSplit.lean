import InfoGeometry.Canonical.OperatorialInformationLift
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.RelativeModularScaleShapeSplit

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialInformationLift
open InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
open InfoGeometry.Canonical.RelativeModularBlockDiagonalCore

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance

/--
Compatibility witness for the operator-lane scale/shape split.
-/
def LiftedScaleShapeCompatibility
    (CIK : CertifiedInverseKernel H₂)
    (H_gen : EndH) : Prop :=
  ∃ (Shape : EndH) (val : ℝ),
    H_gen = Shape + val • (1 : EndH) ∧
    Shape = CIK.spectralProjector * Shape * CIK.spectralProjector

@[rep_depth transport, capstone]
-- theorem-class: existence
theorem operatorial_scaleShapeSplit
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (h : LiftedScaleShapeCompatibility CIK H_gen) :
    ∃ (scalePart shapePart : EndH),
      H_gen = scalePart + shapePart ∧
      (∃ (val : ℝ), scalePart = val • (1 : EndH)) ∧
      shapePart = CIK.spectralProjector * shapePart * CIK.spectralProjector := by
  rcases h with ⟨Shape, val, hEq, hActive⟩
  use val • (1 : EndH), Shape
  refine ⟨?_, ⟨val, rfl⟩, hActive⟩
  rw [add_comm]
  exact hEq

-- theorem-class: closure
theorem drazin_quarantine_annihilates_shape
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (_h : LiftedScaleShapeCompatibility CIK H_gen)
    (shapePart : EndH)
    (hShape : shapePart = CIK.spectralProjector * H_gen * CIK.spectralProjector) :
    (1 - CIK.spectralProjector) * shapePart = 0 := by
  have hOrth :
      CIK.spectralComplementaryProjector * CIK.spectralProjector = 0 :=
    CIK.spectralComplementaryProjector_mul_spectralProjector
  have hShapeDef : shapePart = CIK.spectralProjector * H_gen * CIK.spectralProjector := hShape
  change CIK.spectralComplementaryProjector * shapePart = 0
  rw [hShapeDef]
  calc
    CIK.spectralComplementaryProjector * (CIK.spectralProjector * H_gen) * CIK.spectralProjector
        = ((CIK.spectralComplementaryProjector * CIK.spectralProjector) * H_gen) * CIK.spectralProjector := by
            rw [← mul_assoc]
    _ = ((0 : EndH) * H_gen) * CIK.spectralProjector := by
          rw [hOrth]
    _ = 0 := by
          rw [zero_mul, zero_mul]

/--
Projector-core specialization: when the generator commutes with the active Drazin
projector, the mixed regular/apex blocks vanish.
-/
@[rep_depth transport]
-- theorem-class: closure
theorem mixed_blocks_vanish_of_commute_spectralProjector
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (hComm : Commute CIK.spectralProjector H_gen) :
    CIK.spectralComplementaryProjector * H_gen * CIK.spectralProjector = 0
      ∧
    CIK.spectralProjector * H_gen * CIK.spectralComplementaryProjector = 0 := by
  have hP : CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector :=
    CIK.spectralProjector_idempotent
  have hCore :=
    block_diagonal_of_commute_idempotent
      (E := E) (P := CIK.spectralProjector) (R := H_gen) hP hComm
  constructor
  · calc
      CIK.spectralComplementaryProjector * H_gen * CIK.spectralProjector
          = ((1 : EndH) - CIK.spectralProjector) * H_gen * CIK.spectralProjector := by
              rw [CertifiedInverseKernel.spectralComplementaryProjector,
                CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.1
  · calc
      CIK.spectralProjector * H_gen * CIK.spectralComplementaryProjector
          = CIK.spectralProjector * H_gen * ((1 : EndH) - CIK.spectralProjector) := by
              rw [CertifiedInverseKernel.spectralComplementaryProjector,
                CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hCore.2

@[rep_depth transport, capstone]
-- theorem-class: closure
theorem operatorial_scaleShapeSplit_with_projectorConsequences
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (hCompat : LiftedScaleShapeCompatibility CIK H_gen)
    (hComm : Commute CIK.spectralProjector H_gen) :
    ∃ (scalePart shapePart : EndH),
      H_gen = scalePart + shapePart ∧
      (∃ (val : ℝ), scalePart = val • (1 : EndH)) ∧
      shapePart = CIK.spectralProjector * shapePart * CIK.spectralProjector ∧
      CIK.spectralComplementaryProjector * (CIK.spectralProjector * H_gen * CIK.spectralProjector) = 0 ∧
      (CIK.spectralComplementaryProjector * H_gen * CIK.spectralProjector = 0
        ∧
      CIK.spectralProjector * H_gen * CIK.spectralComplementaryProjector = 0) := by
  have hSplit :=
    operatorial_scaleShapeSplit (E := E) (CIK := CIK) (H_gen := H_gen) hCompat
  have hMixed :=
    mixed_blocks_vanish_of_commute_spectralProjector (E := E) (CIK := CIK) (H_gen := H_gen) hComm
  have hQuarantineRaw :
      (1 - CIK.spectralProjector) * (CIK.spectralProjector * H_gen * CIK.spectralProjector) = 0 :=
    drazin_quarantine_annihilates_shape (E := E) (CIK := CIK) (H_gen := H_gen)
      hCompat (CIK.spectralProjector * H_gen * CIK.spectralProjector) rfl
  have hQuarantine :
      CIK.spectralComplementaryProjector * (CIK.spectralProjector * H_gen * CIK.spectralProjector) = 0 := by
    calc
      CIK.spectralComplementaryProjector * (CIK.spectralProjector * H_gen * CIK.spectralProjector)
          = ((1 : EndH) - CIK.spectralProjector) * (CIK.spectralProjector * H_gen * CIK.spectralProjector) := by
              rw [CertifiedInverseKernel.spectralComplementaryProjector,
                CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
      _ = 0 := hQuarantineRaw
  rcases hSplit with ⟨scalePart, shapePart, hDecomp, hScale, hShape⟩
  exact ⟨scalePart, shapePart, hDecomp, hScale, hShape, hQuarantine, hMixed⟩

end Core

end InfoGeometry.Canonical.RelativeModularScaleShapeSplit
