import InfoGeometry.Canonical.OperatorialInformationLift
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
import InfoGeometry.Canonical.GlobalChiralDecomposition
import InfoGeometry.Canonical.ModularSuperchargeClosure
import InfoGeometry.Canonical.ModularSpectralWedgeBridge
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.RelativeModularScaleShapeSplit

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialInformationLift
open InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
open InfoGeometry.Canonical.RelativeModularBlockDiagonalCore
open InfoGeometry.Canonical.ModularSuperchargeClosure

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

/--
CP-002 operator-level block diagonalization:
the relative modular lane decouples across active/apex projectors when the
generator commutes with the certified spectral projector.
-/
@[rep_depth transport]
-- theorem-class: closure
theorem relativeModular_block_diagonal
    {CIK : CertifiedInverseKernel H₂}
    {R : EndH}
    (hComm : Commute CIK.spectralProjector R) :
    CIK.spectralComplementaryProjector * R * CIK.spectralProjector = 0
      ∧
    CIK.spectralProjector * R * CIK.spectralComplementaryProjector = 0 := by
  exact mixed_blocks_vanish_of_commute_spectralProjector (E := E) (CIK := CIK) (H_gen := R) hComm

/--
CP-002 capstone split: under the same commutation witness, the operator
decomposes into the apex-supported scale block and active-supported shape block.
-/
@[rep_depth transport, capstone]
-- theorem-class: closure
theorem relativeModular_scaleShapeSplit
    {CIK : CertifiedInverseKernel H₂}
    {R : EndH}
    (hComm : Commute CIK.spectralProjector R) :
    R =
      CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector) := by
  let P : EndH := CIK.spectralProjector
  let Q : EndH := CIK.spectralComplementaryProjector
  have hDec : P + Q = (1 : EndH) := by
    simpa [P, Q] using CIK.spectralProjector_add_spectralComplementaryProjector
  have hMixed : Q * R * P = 0 ∧ P * R * Q = 0 := by
    simpa [P, Q] using relativeModular_block_diagonal (E := E) (CIK := CIK) (R := R) hComm
  have hExpand :
      (P + Q) * R * (P + Q)
        = P * (R * P) + (P * (R * Q) + (Q * (R * P) + Q * (R * Q))) := by
    noncomm_ring
  calc
    R = (P + Q) * R * (P + Q) := by
          calc
            R = (1 : EndH) * R * (1 : EndH) := by simp
            _ = (P + Q) * R * (P + Q) := by simpa [hDec]
    _ = P * (R * P) + (P * (R * Q) + (Q * (R * P) + Q * (R * Q))) := hExpand
    _ = P * (R * P) + (0 + (0 + Q * (R * Q))) := by
          have hPRQ : P * (R * Q) = 0 := by
            simpa [mul_assoc] using hMixed.2
          have hQRP : Q * (R * P) = 0 := by
            simpa [mul_assoc] using hMixed.1
          rw [hPRQ, hQRP]
    _ = Q * (R * Q) + P * (R * P) := by
          simp [add_comm]
    _ =
      CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector) := by
          rfl

/--
CP-002 ↔ CP-003 bridge:
from a single commutation witness, expose both split surfaces
(nested projector form and projector-compressed surrogate form).
-/
@[rep_depth transport, capstone]
theorem cp002_cp003_bridge_of_commute
    {CIK : CertifiedInverseKernel H₂}
    {R : EndH}
    (hComm : Commute CIK.spectralProjector R) :
    (R =
      CIK.spectralComplementaryProjector * (R * CIK.spectralComplementaryProjector)
        + CIK.spectralProjector * (R * CIK.spectralProjector))
      ∧
    (R =
      CIK.spectralComplementaryProjector * R * CIK.spectralComplementaryProjector
        + CIK.spectralProjector * R * CIK.spectralProjector) := by
  constructor
  · exact relativeModular_scaleShapeSplit (E := E) (CIK := CIK) (R := R) hComm
  · simpa [mul_assoc] using
      InfoGeometry.Canonical.GlobalChiralDecomposition.global_active_apex_decomposition
        (E := E) (CIK := CIK) (R := R) hComm

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

/--
Bounded operator-level relative modular representative used by CP-002:
the canonical Tomita flow at time `τ`.
-/
@[rep_depth transport]
noncomputable def canonicalRelativeModularOperator
    (CIK : CertifiedInverseKernel H₂) (τ : ℝ) : EndH :=
  (canonicalTomitaLogData (E := E) CIK).flow τ

/--
Commutation witness for CP-002 Phase A:
on a wedge-calibrated canonical lane, the bounded relative modular
representative commutes with the active Drazin projector.
-/
@[rep_depth transport]
theorem canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    Commute
      (canonicalRelativeModularOperator (E := E) CIK τ)
      CIK.spectralProjector := by
  have hActive :
      (canonicalTomitaLogData (E := E) CIK).flow τ
          * ((1 : EndH) - CIK.spectralComplementaryProjector)
        =
      ((1 : EndH) - CIK.spectralComplementaryProjector)
          * (canonicalTomitaLogData (E := E) CIK).flow τ :=
    canonicalTomitaFlow_commutes_activeProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  have hProj :
      ((1 : EndH) - CIK.spectralComplementaryProjector) = CIK.spectralProjector := by
    rw [CertifiedInverseKernel.spectralComplementaryProjector,
      CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
    simp
  simpa [Commute, canonicalRelativeModularOperator, hProj] using hActive

/--
CP-002 Phase A (operator lane):
the canonical bounded relative modular representative decomposes into
apex-supported and active-supported blocks on a wedge-calibrated lane.
-/
@[rep_depth transport, capstone]
theorem canonicalRelativeModularOperator_scaleShapeSplit_of_wedgeCalibrated
    (CIK : CertifiedInverseKernel H₂)
    {W : InfoGeometry.Canonical.ModularSpectralWedge.HasModularSpectralWedge E}
    (C :
      InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
        (E := E)
        (T := canonicalTomitaLogData (E := E) CIK)
        (W := W)
        (owned_epsilon := spectral_epsilon (E := E))
        (owned_P_D := CIK.spectralComplementaryProjector))
    (τ : ℝ) :
    canonicalRelativeModularOperator (E := E) CIK τ
      =
    CIK.spectralComplementaryProjector
        * canonicalRelativeModularOperator (E := E) CIK τ
        * CIK.spectralComplementaryProjector
      +
    CIK.spectralProjector
        * canonicalRelativeModularOperator (E := E) CIK τ
        * CIK.spectralProjector := by
  have hComm :
      Commute
        (canonicalRelativeModularOperator (E := E) CIK τ)
        CIK.spectralProjector :=
    canonicalRelativeModularOperator_commutes_spectralProjector_of_wedgeCalibrated
      (E := E) (CIK := CIK) (W := W) C τ
  have hSplit :=
    relativeModular_scaleShapeSplit
      (E := E) (CIK := CIK)
      (R := canonicalRelativeModularOperator (E := E) CIK τ)
      hComm.symm
  simpa [mul_assoc] using hSplit

end Core

end InfoGeometry.Canonical.RelativeModularScaleShapeSplit
