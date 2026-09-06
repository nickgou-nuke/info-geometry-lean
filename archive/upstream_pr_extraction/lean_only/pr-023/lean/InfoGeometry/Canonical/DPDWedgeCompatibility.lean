import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.ModularSpectralWedge
import InfoGeometry.Canonical.ModularSpectralWedgeBridge
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic.NoncommRing

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DPDWedgeCompatibility

open InfoGeometry.Krein
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ModularSpectralWedge

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

/--
Compatibility relation between the DPD projected split and a modular spectral
wedge split:
`P_R = PiPlus`, `P_L = PiMinus`, `P_0 = PZero`.
-/
@[rep_depth transport]
structure IsCompatibleDPDWedge
    (CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E))
    (W : HasModularSpectralWedge E) : Prop where
  hPlus : CIK.mpRangeProjector = W.PiPlus
  hMinus : CIK.metricProjector = W.PiMinus
  hZero : CIK.spectralComplementaryProjector = W.PZero

namespace IsCompatibleDPDWedge

variable {CIK : InfoGeometry.Canonical.CertifiedInverseKernel (InfoGeometry.Krein.DoubledSpace E)}
variable {W : HasModularSpectralWedge E}

/--
Kernel/sign convention lock on the compatible DPD/wedge lane:
the wedge-kernel projector is exactly the certified Drazin complementary
projector `Q_D := 1 - P_D`.
-/
@[rep_depth transport]
theorem kernelConventionLock_pzero_eq_spectralComplementaryProjector
    (comp : IsCompatibleDPDWedge CIK W) :
    W.PZero = CIK.spectralComplementaryProjector := by
  simpa using comp.hZero.symm

/--
Active projector lock on the compatible lane:
`P_active = 1 - Q_D`.
-/
@[rep_depth transport]
theorem activeProjector_eq_one_sub_spectralComplementaryProjector
    (comp : IsCompatibleDPDWedge CIK W) :
    W.activeProjector = (1 : EndH) - CIK.spectralComplementaryProjector := by
  unfold HasModularSpectralWedge.activeProjector
  apply eq_sub_iff_add_eq.mpr
  calc
    W.PiPlus + W.PiMinus + CIK.spectralComplementaryProjector
        = W.PiPlus + W.PiMinus + W.PZero := by
            simp [comp.hZero]
    _ = (1 : EndH) := by
          simpa [add_assoc] using W.resolution

/--
With the kernel convention lock, the wedge sign squares to the certified
regular Drazin projector:
`ε_wedge^2 = P_D`.
-/
@[rep_depth transport]
theorem wedgeSign_sq_eq_spectralProjector
    (comp : IsCompatibleDPDWedge CIK W) :
    W.wedgeSign * W.wedgeSign = CIK.spectralProjector := by
  calc
    W.wedgeSign * W.wedgeSign
        = (1 : EndH) - W.PZero := W.wedgeSign_sq
    _ = (1 : EndH) - CIK.spectralComplementaryProjector := by
          simp [comp.hZero]
    _ = CIK.spectralProjector := by
          change (1 : EndH)
              - (1 - CIK.spectralProjector)
              = CIK.spectralProjector
          simp

/--
Kernel annihilation on the right:
`ε_wedge * Q_D = 0`.
-/
@[rep_depth transport]
theorem wedgeSign_mul_spectralComplementaryProjector_eq_zero
    (comp : IsCompatibleDPDWedge CIK W) :
    W.wedgeSign * CIK.spectralComplementaryProjector = 0 := by
  rw [comp.hZero]
  unfold HasModularSpectralWedge.wedgeSign
  calc
    (W.PiPlus - W.PiMinus) * W.PZero
        = W.PiPlus * W.PZero - W.PiMinus * W.PZero := by
            simp [sub_mul]
    _ = 0 - 0 := by rw [W.PiPlus_PZero, W.PiMinus_PZero]
    _ = 0 := by simp

/--
Kernel annihilation on the left:
`Q_D * ε_wedge = 0`.
-/
@[rep_depth transport]
theorem spectralComplementaryProjector_mul_wedgeSign_eq_zero
    (comp : IsCompatibleDPDWedge CIK W) :
    CIK.spectralComplementaryProjector * W.wedgeSign = 0 := by
  rw [comp.hZero]
  unfold HasModularSpectralWedge.wedgeSign
  calc
    W.PZero * (W.PiPlus - W.PiMinus)
        = W.PZero * W.PiPlus - W.PZero * W.PiMinus := by
            simp [mul_sub]
    _ = 0 - 0 := by rw [W.PZero_PiPlus, W.PZero_PiMinus]
    _ = 0 := by simp

/--
`ε_wedge` is involutive on the active regular lane:
right restriction to `P_D` is fixed.
-/
@[rep_depth transport]
theorem wedgeSign_sq_mul_spectralProjector_eq_spectralProjector
    (comp : IsCompatibleDPDWedge CIK W) :
    (W.wedgeSign * W.wedgeSign) * CIK.spectralProjector = CIK.spectralProjector := by
  rw [wedgeSign_sq_eq_spectralProjector (CIK := CIK) (W := W) comp]
  simpa using CIK.spectralProjector_idempotent

/--
On a compatible DPD/wedge lane, the DPD dilation generator satisfies
`2G = ε_wedge`.
-/
@[rep_depth transport]
theorem two_smul_dilationGap_eq_wedgeSign
    (comp : IsCompatibleDPDWedge CIK W) :
    (2 : ℝ) • CIK.dilationGap = W.wedgeSign := by
  calc
    (2 : ℝ) • CIK.dilationGap = CIK.mpRangeProjector - CIK.metricProjector := by
          symm
          exact CIK.mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap
    _ = W.PiPlus - W.PiMinus := by simp [comp.hPlus, comp.hMinus]
    _ = W.wedgeSign := by
          simp [HasModularSpectralWedge.wedgeSign]

/--
Equivalent half-scale wedge form of the DPD dilation generator:
`G = (1/2) ε_wedge`.
-/
@[rep_depth transport]
theorem dilationGap_eq_half_wedgeSign
    (comp : IsCompatibleDPDWedge CIK W) :
    CIK.dilationGap = ((2 : ℝ)⁻¹) • W.wedgeSign := by
  have hTwo : (2 : ℝ)⁻¹ * (2 : ℝ) = 1 := by norm_num
  calc
    CIK.dilationGap = ((2 : ℝ)⁻¹ * (2 : ℝ)) • CIK.dilationGap := by
          simp
    _ = (2 : ℝ)⁻¹ • ((2 : ℝ) • CIK.dilationGap) := by
          simp [smul_smul]
    _ = (2 : ℝ)⁻¹ • W.wedgeSign := by
          rw [two_smul_dilationGap_eq_wedgeSign comp]

/--
Canonical constructor from a DPD/wedge compatibility witness to the wedge-flow
calibration packet used on the modular spectral bridge lane.
-/
@[rep_depth transport]
theorem wedgeCalibrated_of_compatibleDPDWedge
    (T : InfoGeometry.Canonical.RealTomitaCore.RealModularLogData (E := E))
    (comp : IsCompatibleDPDWedge CIK W)
    (hFlowCommQd : ∀ τ : ℝ, Commute (T.flow τ) CIK.spectralComplementaryProjector)
    (hFlowCommEps :
      ∀ τ : ℝ, Commute (T.flow τ) ((2 : ℝ) • CIK.dilationGap)) :
    InfoGeometry.Canonical.ModularSpectralWedgeBridge.WedgeCalibrated
      (E := E) (T := T) (W := W)
      ((2 : ℝ) • CIK.dilationGap) CIK.spectralComplementaryProjector := by
  refine
    { compat :=
        { epsilon_eq := ?_
          pzero_eq := comp.hZero.symm }
      flow_commutes_owned_P_D := hFlowCommQd
      flow_commutes_owned_epsilon := hFlowCommEps }
  simpa using (two_smul_dilationGap_eq_wedgeSign (CIK := CIK) (W := W) comp).symm

/--
Projected supercharge bridge to the modular wedge sign on the regular Drazin lane:
`Q_D = [P_reg, ε_wedge]`.
-/
@[rep_depth transport, capstone]
theorem projected_supercharge_eq_commutator_PD_wedgeSign
    (comp : IsCompatibleDPDWedge CIK W) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
  calc
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = (2 : ℝ) • InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector CIK.dilationGap := by
            exact
              InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_two_smul_commutator_spectralProjector_dilationGap
                (CIK := CIK)
    _ = InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector ((2 : ℝ) • CIK.dilationGap) := by
          unfold InfoGeometry.Canonical.DrazinSupercharge.commutator
          simp [smul_sub]
    _ = InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
          rw [two_smul_dilationGap_eq_wedgeSign comp]

/--
Complementary-apex form (with repo orientation): the same bridge on `P_0`
appears with a sign flip:
`Q_D = -[P_0, ε_wedge]`, where `P_0 = 1 - P_reg`.
-/
@[rep_depth transport, capstone]
theorem projected_supercharge_eq_neg_commutator_PZero_wedgeSign
    (comp : IsCompatibleDPDWedge CIK W) :
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
      =
    -InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralComplementaryProjector W.wedgeSign := by
  have hComm :
      InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralComplementaryProjector W.wedgeSign
        =
      -InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
    unfold InfoGeometry.Canonical.DrazinSupercharge.commutator
    change
      ((1 : EndH) - CIK.spectralProjector) * W.wedgeSign
        - W.wedgeSign * ((1 : EndH) - CIK.spectralProjector)
        =
      -(CIK.spectralProjector * W.wedgeSign - W.wedgeSign * CIK.spectralProjector)
    noncomm_ring
  calc
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
            exact projected_supercharge_eq_commutator_PD_wedgeSign
              comp
    _ = -InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralComplementaryProjector W.wedgeSign := by
          rw [hComm]
          simp

/--
Kernel-supported (`Q_D`) scale block of a relative modular operator candidate.
-/
@[rep_depth transport]
noncomputable def relativeModularKernelScalePart
    (RMO : EndH) : EndH :=
  CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector

/--
Active (`P_D`) projective-shape block of a relative modular operator candidate.
-/
@[rep_depth transport]
noncomputable def relativeModularActiveShapePart
    (RMO : EndH) : EndH :=
  CIK.spectralProjector * RMO * CIK.spectralProjector

/--
If a relative modular operator candidate commutes with the certified active
projector `P_D`, then both mixed Drazin blocks vanish.
-/
@[rep_depth transport]
theorem relativeModular_offDiagonal_blocks_zero_of_commutes_spectralProjector
    {RMO : EndH}
    (hComm : Commute RMO CIK.spectralProjector) :
    CIK.spectralComplementaryProjector * RMO * CIK.spectralProjector = 0
      ∧
    CIK.spectralProjector * RMO * CIK.spectralComplementaryProjector = 0 := by
  constructor
  · calc
      CIK.spectralComplementaryProjector * RMO * CIK.spectralProjector
          = CIK.spectralComplementaryProjector * (RMO * CIK.spectralProjector) := by
              simp [mul_assoc]
      _ = CIK.spectralComplementaryProjector * (CIK.spectralProjector * RMO) := by
            rw [hComm.eq]
      _ = (CIK.spectralComplementaryProjector * CIK.spectralProjector) * RMO := by
            simp [mul_assoc]
      _ = 0 := by
            simp [CIK.spectralComplementaryProjector_mul_spectralProjector]
  · calc
      CIK.spectralProjector * RMO * CIK.spectralComplementaryProjector
          = (CIK.spectralProjector * RMO) * CIK.spectralComplementaryProjector := by
              simp [mul_assoc]
      _ = (RMO * CIK.spectralProjector) * CIK.spectralComplementaryProjector := by
            rw [hComm.eq.symm]
      _ = RMO * (CIK.spectralProjector * CIK.spectralComplementaryProjector) := by
            simp [mul_assoc]
      _ = 0 := by
            simp [CIK.spectralProjector_mul_spectralComplementaryProjector]

/--
Operatorial scale/shape split on the Drazin lane:
if mixed blocks vanish, the relative modular operator candidate decomposes as
`RMO = Q_D RMO Q_D + P_D RMO P_D`.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit
    {RMO : EndH}
    (hQD_RMO_PD_zero :
      CIK.spectralComplementaryProjector * RMO * CIK.spectralProjector = 0)
    (hPD_RMO_QD_zero :
      CIK.spectralProjector * RMO * CIK.spectralComplementaryProjector = 0) :
    RMO
      =
    relativeModularKernelScalePart (CIK := CIK) RMO
      +
    relativeModularActiveShapePart (CIK := CIK) RMO := by
  have hSplit :
      CIK.spectralProjector + CIK.spectralComplementaryProjector = (1 : EndH) :=
    CIK.spectralProjector_add_spectralComplementaryProjector
  calc
    RMO = (1 : EndH) * RMO * (1 : EndH) := by simp
    _ =
      (CIK.spectralProjector + CIK.spectralComplementaryProjector)
        * RMO *
      (CIK.spectralProjector + CIK.spectralComplementaryProjector) := by
        simp [hSplit]
    _ =
      ((CIK.spectralProjector * RMO * CIK.spectralProjector)
        + (CIK.spectralProjector * RMO * CIK.spectralComplementaryProjector))
        +
      ((CIK.spectralComplementaryProjector * RMO * CIK.spectralProjector)
        + (CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector)) := by
        noncomm_ring
    _ =
      ((CIK.spectralProjector * RMO * CIK.spectralProjector) + 0)
        +
      (0 + (CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector)) := by
        rw [hPD_RMO_QD_zero, hQD_RMO_PD_zero]
    _ =
      CIK.spectralProjector * RMO * CIK.spectralProjector
        + CIK.spectralComplementaryProjector * RMO * CIK.spectralComplementaryProjector := by
        simp
    _ =
      relativeModularKernelScalePart (CIK := CIK) RMO
        + relativeModularActiveShapePart (CIK := CIK) RMO := by
        rw [add_comm]
        rfl

/--
Derived block split from the commuting criterion:
`[RMO, P_D] = 0` implies the canonical Drazin scale/shape decomposition.
-/
@[rep_depth transport, capstone]
theorem relativeModular_scaleShapeSplit_of_commutes_spectralProjector
    {RMO : EndH}
    (hComm : Commute RMO CIK.spectralProjector) :
    RMO
      =
    relativeModularKernelScalePart (CIK := CIK) RMO
      +
    relativeModularActiveShapePart (CIK := CIK) RMO := by
  rcases
      relativeModular_offDiagonal_blocks_zero_of_commutes_spectralProjector
        (CIK := CIK) hComm with
    ⟨hQD_RMO_PD_zero, hPD_RMO_QD_zero⟩
  exact relativeModular_scaleShapeSplit
      (CIK := CIK)
      (hQD_RMO_PD_zero := hQD_RMO_PD_zero)
      (hPD_RMO_QD_zero := hPD_RMO_QD_zero)

end IsCompatibleDPDWedge

end Core

end InfoGeometry.Canonical.DPDWedgeCompatibility
