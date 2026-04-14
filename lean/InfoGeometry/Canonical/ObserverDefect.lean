import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.ObserverDefect

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Local observer slice that preserves the spectral grading orientation.
-/
structure ObserverL5 (CIK : CertifiedInverseKernel H₂) where
  localSlice : EndH
  isOrientationFixing :
    localSlice * CIK.toInformationCartanTriple.GammaS =
      CIK.toInformationCartanTriple.GammaS * localSlice

/--
Primary observer residual against the geometric dilation lane.
-/
noncomputable def observerOrientationResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : EndH :=
  DrazinSupercharge.commutator obs.localSlice CIK.dilationGap

/--
Defect-compressed observer residual in the Drazin complementary block.
-/
noncomputable def observerDefectResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : EndH :=
  CIK.spectralComplementaryProjector *
    observerOrientationResidual CIK obs *
    CIK.spectralComplementaryProjector

/--
Defect compression is stable under left/right `Q₀` action.
-/
theorem observerDefectResidual_isDefectSupported
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    CIK.spectralComplementaryProjector * observerDefectResidual CIK obs
      = observerDefectResidual CIK obs
      ∧
    observerDefectResidual CIK obs * CIK.spectralComplementaryProjector
      = observerDefectResidual CIK obs := by
  unfold observerDefectResidual
  constructor
  · calc
      CIK.spectralComplementaryProjector *
          (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
            CIK.spectralComplementaryProjector)
          =
        (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) *
          observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]
  · calc
      (CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector) *
        CIK.spectralComplementaryProjector
          =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * observerOrientationResidual CIK obs *
          CIK.spectralComplementaryProjector := by
            simp [CIK.spectralComplementaryProjector_idempotent]

/--
Defect residual commutes with the complementary projector.
-/
theorem observerDefectResidual_commutes_complementaryProjector
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    Commute (observerDefectResidual CIK obs) CIK.spectralComplementaryProjector := by
  have h := observerDefectResidual_isDefectSupported (CIK := CIK) (obs := obs)
  calc
    observerDefectResidual CIK obs * CIK.spectralComplementaryProjector
      = observerDefectResidual CIK obs := h.2
    _ = CIK.spectralComplementaryProjector * observerDefectResidual CIK obs := h.1.symm

/--
Aligned observer (zero primary residual) yields zero defect residual.
-/
theorem observerDefectResidual_eq_zero_of_aligned
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    observerDefectResidual CIK obs = 0 := by
  unfold observerDefectResidual
  simp [hAlign]

/--
Scalarized observer strain (pre-thermodynamic cost) via operator norm.
-/
noncomputable def observerOrientationStrain
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : ℝ :=
  ‖observerDefectResidual CIK obs‖

/--
Zero strain iff zero defect residual.
-/
theorem observerOrientationStrain_eq_zero_iff
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) :
    observerOrientationStrain CIK obs = 0 ↔ observerDefectResidual CIK obs = 0 := by
  simpa [observerOrientationStrain] using
    (ContinuousLinearMap.opNorm_zero_iff (f := observerDefectResidual CIK obs))

end Core

end InfoGeometry.Canonical.ObserverDefect
