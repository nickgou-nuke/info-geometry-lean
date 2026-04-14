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
Generic two-block decoupling:
if `P^2 = P` and `P` commutes with `R`, then off-diagonal blocks vanish.
-/
@[rep_depth transport]
theorem block_diagonal_of_commute_idempotent
    (P R : EndH)
    (hP : P * P = P)
    (hPR : Commute P R) :
    ((1 : EndH) - P) * R * P = 0
      ∧
    P * R * ((1 : EndH) - P) = 0 := by
  constructor
  · calc
      ((1 : EndH) - P) * R * P
          = R * P - P * R * P := by
              simp [sub_mul, mul_assoc]
      _ = R * P - R * P := by
            simp [hPR.eq, mul_assoc, hP]
      _ = 0 := sub_self _
  · calc
      P * R * ((1 : EndH) - P)
          = P * R - P * R * P := by
              simp [mul_sub, mul_assoc]
      _ = P * R - P * R := by
            simp [hPR.eq, mul_assoc, hP]
      _ = 0 := sub_self _

/--
Block-diagonality witness on the Drazin split.
This is the CP-002 off-diagonal vanishing lock.
-/
@[rep_depth transport]
theorem relativeModular_block_diagonal
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH)
    (hComm : Commute RMO (activeProjector (E := E) CIK)) :
    kernelProjector (E := E) CIK * RMO * activeProjector (E := E) CIK = 0
      ∧
    activeProjector (E := E) CIK * RMO * kernelProjector (E := E) CIK = 0 := by
  have hIdem :
      activeProjector (E := E) CIK * activeProjector (E := E) CIK
        = activeProjector (E := E) CIK := by
    simpa [activeProjector] using CIK.spectralProjector_idempotent
  have hBlocks :=
    block_diagonal_of_commute_idempotent
      (E := E) (P := activeProjector (E := E) CIK) (R := RMO)
      hIdem hComm.symm
  simpa [kernelProjector, activeProjector, CertifiedInverseKernel.spectralComplementaryProjector,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.spectralComplementaryProjector]
    using hBlocks

/--
Alias preserving the old CP-002 theorem name for downstream compatibility.
-/
@[rep_depth transport]
theorem relativeModular_crossTerms_zero_of_commutes_activeProjector
    (CIK : CertifiedInverseKernel H₂)
    (RMO : EndH)
    (hComm : Commute RMO (activeProjector (E := E) CIK)) :
    kernelProjector (E := E) CIK * RMO * activeProjector (E := E) CIK = 0
      ∧
    activeProjector (E := E) CIK * RMO * kernelProjector (E := E) CIK = 0 := by
  exact relativeModular_block_diagonal (E := E) (CIK := CIK) (RMO := RMO) hComm

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
  constructor
  · unfold kernelProjector relativeModularScalePart
    calc
      CIK.spectralComplementaryProjector
          * (IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO)
          =
        (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector)
          * RMO * CIK.spectralComplementaryProjector := by
            simp [IsCompatibleDPDWedge.relativeModularKernelScalePart, mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector := by
          simp [CIK.spectralComplementaryProjector_idempotent]
      _ = IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO := by
          simp [IsCompatibleDPDWedge.relativeModularKernelScalePart]
  · unfold kernelProjector relativeModularScalePart
    calc
      (IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO)
          * CIK.spectralComplementaryProjector
          =
        CIK.spectralComplementaryProjector * RMO
          * (CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector) := by
            simp [IsCompatibleDPDWedge.relativeModularKernelScalePart, mul_assoc]
      _ =
        CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector := by
          simp [CIK.spectralComplementaryProjector_idempotent]
      _ = IsCompatibleDPDWedge.relativeModularKernelScalePart (CIK := CIK) RMO := by
          simp [IsCompatibleDPDWedge.relativeModularKernelScalePart]

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
  constructor
  · unfold activeProjector relativeModularShapePart
    calc
      CIK.spectralProjector
          * (IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO)
          =
        (CIK.spectralProjector * CIK.spectralProjector)
          * RMO * CIK.spectralProjector := by
            simp [IsCompatibleDPDWedge.relativeModularActiveShapePart, mul_assoc]
      _ =
        CIK.spectralProjector * RMO * CIK.spectralProjector := by
          simp [CIK.spectralProjector_idempotent]
      _ = IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO := by
          simp [IsCompatibleDPDWedge.relativeModularActiveShapePart]
  · unfold activeProjector relativeModularShapePart
    calc
      (IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO)
          * CIK.spectralProjector
          =
        CIK.spectralProjector * RMO
          * (CIK.spectralProjector * CIK.spectralProjector) := by
            simp [IsCompatibleDPDWedge.relativeModularActiveShapePart, mul_assoc]
      _ =
        CIK.spectralProjector * RMO * CIK.spectralProjector := by
          simp [CIK.spectralProjector_idempotent]
      _ = IsCompatibleDPDWedge.relativeModularActiveShapePart (CIK := CIK) RMO := by
          simp [IsCompatibleDPDWedge.relativeModularActiveShapePart]

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

/--
Phase B capstone in commutation form:
from `[RMO, P_D] = 0`, derive both the operatorial scale/shape split and the
strict-positive projective/gauge comparison package on the compatible DPD/wedge
lane.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit_of_commutes_activeProjector
    (CIK : CertifiedInverseKernel H₂)
    (W : HasModularSpectralWedge E)
    (comp : IsCompatibleDPDWedge (E := E) CIK W)
    (RMO : EndH)
    (hComm : Commute RMO (activeProjector (E := E) CIK))
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
  rcases relativeModular_crossTerms_zero_of_commutes_activeProjector
      (E := E) (CIK := CIK) (RMO := RMO) hComm with ⟨hQP, hPQ⟩
  exact relativeModular_scaleShapeSplit_eq_projectiveGaugeSplit
      (E := E) (α := α) CIK W comp RMO hQP hPQ μ ν

end Core

end InfoGeometry.Canonical.RelativeModularScaleShapeSplit
