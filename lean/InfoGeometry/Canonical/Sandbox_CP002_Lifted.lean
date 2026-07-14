import InfoGeometry.Canonical.OperatorialInformationLift
import InfoGeometry.Canonical.KreinDiracWeightFunctionalLift
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace Sandbox_CP002_Lifted

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorialInformationLift
open InfoGeometry.Canonical.KreinDiracWeightFunctionalLift

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Lifted compatibility predicate for the Drazin-Modular Scale-Shape split.
Operates on the full doubled carrier H₂.
-/
structure LiftedScaleShapeCompatibility
    (CIK : CertifiedInverseKernel H₂)
    (H_gen : EndH) where
  /-- The generator decomposes into a shape part and a scale (identity) part. -/
  hSplit : ∃ (Shape : EndH) (val : ℝ),
    H_gen = Shape + val • (1 : EndH) ∧
    Commute Shape CIK.spectralProjector ∧
    Shape = CIK.spectralProjector * Shape * CIK.spectralProjector

/--
The Master Operatorial Scale-Shape Split.

This theorem proves that the physical generator H_gen on the doubled carrier
admits a canonical split into a Drazin-regularized Shape and a scalar Scale.
-/
@[rep_depth transport, capstone]
theorem operatorial_scaleShapeSplit
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (h : LiftedScaleShapeCompatibility CIK H_gen) :
    ∃ (scalePart shapePart : EndH),
      H_gen = scalePart + shapePart ∧
      (∃ (val : ℝ), scalePart = val • (1 : EndH)) ∧
      shapePart = CIK.spectralProjector * shapePart * CIK.spectralProjector := by
  rcases h.hSplit with ⟨Shape, val, hEq, _, hActive⟩
  let scale := val • (1 : EndH)
  let shape := Shape
  use scale, shape
  refine ⟨?_, ⟨val, rfl⟩, hActive⟩
  rw [add_comm]
  exact hEq

/--
Nomological Closure: The Drazin complementary projector (quarantine) annihilates
 the shape part of the modular generator.
-/
theorem drazin_quarantine_annihilates_shape
    {CIK : CertifiedInverseKernel H₂}
    {H_gen : EndH}
    (_h : LiftedScaleShapeCompatibility CIK H_gen)
    (shapePart : EndH)
    (hShape : shapePart = CIK.spectralProjector * H_gen * CIK.spectralProjector) :
    (1 - CIK.spectralProjector) * shapePart = 0 := by
  change CIK.spectralComplementaryProjector * shapePart = 0
  have hShape' :
      shapePart = CIK.spectralProjector * (H_gen * CIK.spectralProjector) := by
    simpa [mul_assoc] using hShape
  rw [hShape', ← mul_assoc, CIK.spectralComplementaryProjector_mul_spectralProjector]
  simp

end Core

end Sandbox_CP002_Lifted
