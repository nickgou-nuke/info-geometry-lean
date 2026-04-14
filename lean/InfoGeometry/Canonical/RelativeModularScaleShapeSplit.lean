import InfoGeometry.Canonical.DPDWedgeCompatibility
import InfoGeometry.Canonical.ModularKLDivergenceBridge
import InfoGeometry.Meta.Architecture

open scoped ENNReal NNReal InnerProductSpace

/-!
# InfoGeometry.Canonical.RelativeModularScaleShapeSplit

Owner-level CP-002 surface for the relative modular scale/shape split.

This file adds no new ontology. It packages the already-certified Drazin/wedge
operatorial split and the strict-positive projective/gauge comparison theorem
into a dedicated capstone namespace.
-/

namespace InfoGeometry.Canonical.RelativeModularScaleShapeSplit

open InfoGeometry.Krein
open InfoGeometry.PositiveMeasure
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DPDWedgeCompatibility
open InfoGeometry.Canonical.ModularSpectralWedge
open InfoGeometry.Canonical.ModularKLDivergenceBridge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {α : Type*} [Fintype α] [Nonempty α]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

private noncomputable instance : NormedRing EndH := inferInstance
private noncomputable instance : NormedAlgebra ℝ EndH := inferInstance
private instance : IsTopologicalRing EndH := inferInstance
private instance : CompleteSpace EndH := inferInstance
private instance : SMulCommClass ℝ EndH EndH := inferInstance
private instance : IsScalarTower ℝ EndH EndH := inferInstance

/-- Apex/kernel projector (`Q_D`) in the CP-002 split. -/
@[rep_depth transport, simp]
noncomputable abbrev kernelProjector
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  CIK.spectralComplementaryProjector

/-- Active regular projector (`P_D`) in the CP-002 split. -/
@[rep_depth transport, simp]
noncomputable abbrev activeProjector
    (CIK : CertifiedInverseKernel H₂) : EndH :=
  CIK.spectralProjector

/-- Kernel-supported scale block `Q_D * RMO * Q_D`. -/
@[rep_depth transport]
noncomputable abbrev relativeModularScalePart
    (CIK : CertifiedInverseKernel H₂) (RMO : EndH) : EndH :=
  IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO

/-- Active-supported shape block `P_D * RMO * P_D`. -/
@[rep_depth transport]
noncomputable abbrev relativeModularShapePart
    (CIK : CertifiedInverseKernel H₂) (RMO : EndH) : EndH :=
  IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO

/--
Block-diagonality witness on the Drazin split.
This is the CP-002 off-diagonal vanishing lock.
-/
@[rep_depth transport]
theorem relativeModular_crossTerms_zero_of_commutes_activeProjector
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH)
    (hComm : Commute RMO (activeProjector (E := E) CIK)) :
    kernelProjector (E := E) CIK * RMO * activeProjector (E := E) CIK = 0
      ∧
    activeProjector (E := E) CIK * RMO * kernelProjector (E := E) CIK = 0 := by
  simpa [kernelProjector, activeProjector] using
    IsCompatibleDPDWedge.relativeModular_offDiagonal_blocks_zero_of_commutes_spectralProjector
      (CIK := CIK) (RMO := RMO) hComm

/-- Kernel support of the CP-002 scale block. -/
@[rep_depth transport]
theorem relativeModular_scalePart_supported_on_kernel
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH) :
    kernelProjector (E := E) CIK
        * relativeModularScalePart (E := E) CIK RMO
      = relativeModularScalePart (E := E) CIK RMO
      ∧
    relativeModularScalePart (E := E) CIK RMO
        * kernelProjector (E := E) CIK
      = relativeModularScalePart (E := E) CIK RMO := by
  constructor <;> simp [kernelProjector, relativeModularScalePart, mul_assoc,
    CIK.spectralComplementaryProjector_idempotent]

/-- Active support of the CP-002 shape block. -/
@[rep_depth transport]
theorem relativeModular_shapePart_supported_on_active
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH) :
    activeProjector (E := E) CIK
        * relativeModularShapePart (E := E) CIK RMO
      = relativeModularShapePart (E := E) CIK RMO
      ∧
    relativeModularShapePart (E := E) CIK RMO
        * activeProjector (E := E) CIK
      = relativeModularShapePart (E := E) CIK RMO := by
  constructor <;> simp [activeProjector, relativeModularShapePart, mul_assoc,
    CIK.spectralProjector_idempotent]

/--
Operatorial CP-002 capstone:
`RMO = Q_D RMO Q_D + P_D RMO P_D` once mixed blocks vanish.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH)
    (hQD_RMO_PD_zero :
      kernelProjector (E := E) CIK * RMO * activeProjector (E := E) CIK = 0)
    (hPD_RMO_QD_zero :
      activeProjector (E := E) CIK * RMO * kernelProjector (E := E) CIK = 0) :
    RMO
      =
    relativeModularScalePart (E := E) CIK RMO
      +
    relativeModularShapePart (E := E) CIK RMO := by
  exact IsCompatibleDPDWedge.relativeModular_scaleShapeSplit
      (CIK := CIK)
      (hQD_RMO_PD_zero := hQD_RMO_PD_zero)
      (hPD_RMO_QD_zero := hPD_RMO_QD_zero)

/--
Commutation-form CP-002 capstone:
`[RMO, P_D] = 0` implies the same scale/shape decomposition.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_of_commutes_activeProjector
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH)
    (hComm : Commute RMO (activeProjector (E := E) CIK)) :
    RMO
      =
    relativeModularScalePart (E := E) CIK RMO
      +
    relativeModularShapePart (E := E) CIK RMO := by
  rcases relativeModular_crossTerms_zero_of_commutes_activeProjector
      (E := E) (CIK := CIK) (RMO := RMO) hComm with ⟨hQP, hPQ⟩
  exact relativeModular_scaleShapeSplit
      (E := E) (CIK := CIK) (RMO := RMO) hQP hPQ

/--
CP-002 comparison theorem:
the operatorial Drazin block split and the strict-positive projective/gauge
split are packaged on the same compatible DPD/wedge lane.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit
    (CIK : CertifiedInverseKernel H₂)
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (RMO : EndH)
    (hQD_RMO_PD_zero :
      kernelProjector (E := E) CIK * RMO * activeProjector (E := E) CIK = 0)
    (hPD_RMO_QD_zero :
      activeProjector (E := E) CIK * RMO * kernelProjector (E := E) CIK = 0)
    (μ ν : PositiveMeasure α ℝ) :
    RMO
      =
    relativeModularScalePart (E := E) CIK RMO
      +
    relativeModularShapePart (E := E) CIK RMO
      ∧
    generalizedKL (α := α) μ ν
      =
    generalizedKL_activeShapeTerm (α := α) μ ν
      + generalizedKL_kernelMassTerm (α := α) μ ν
      ∧
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector
      ∧
    CIK.spectralComplementaryProjector = W.PZero := by
  exact ModularKLDivergenceBridge.relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit
      (E := E) (α := α) CIK W comp RMO hQD_RMO_PD_zero hPD_RMO_QD_zero μ ν

end Core

end InfoGeometry.Canonical.RelativeModularScaleShapeSplit
