import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.InverseKernelAlgebra
import InfoGeometry.Canonical.ModularSpectralWedge
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
      (CIK.spectralComplementaryProjector * W.wedgeSign
        - W.wedgeSign * CIK.spectralComplementaryProjector)
        =
      -(CIK.spectralProjector * W.wedgeSign - W.wedgeSign * CIK.spectralProjector)
    simp [CertifiedInverseKernel.spectralComplementaryProjector,
      CertifiedInverseKernel.toInverseKernel',
      InverseKernel.spectralComplementaryProjector]
    noncomm_ring
  calc
    InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.supercharge CIK
        = InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralProjector W.wedgeSign := by
            exact projected_supercharge_eq_commutator_PD_wedgeSign
              comp
    _ = -InfoGeometry.Canonical.DrazinSupercharge.commutator CIK.spectralComplementaryProjector W.wedgeSign := by
          rw [hComm]
          simp

end IsCompatibleDPDWedge

end Core

end InfoGeometry.Canonical.DPDWedgeCompatibility
