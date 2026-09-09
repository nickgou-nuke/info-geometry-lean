import InfoGeometry.Canonical.DrazinDilationGap
import InfoGeometry.Canonical.DrazinPenroseDilationAlgebra
import InfoGeometry.Canonical.DrazinSupercharge
import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinDilationGapBridge

Black-Book-safe bridge from the generic dilation-gap socket to the repository
owned `CertifiedInverseKernel` Drazin supercharge lane.

The theorem-owned identities here are:

* `G = 1/2 • (P_R - P_L)`;
* `[P_D, G] = 1/2 • (χ_R - χ_L)`;
* `Q_D = χ_R - χ_L`;
* `Γ_G = 2 • G`;
* `Q_D = 2 • [P_D, G]`;
* `Q_D = [P_D, Γ_G]`;
* `{Γ_S, Q_D} = 0`.

This file does not assert that every certified kernel automatically carries a
thermodynamic heat/memory split.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Canonical.DrazinDilationGapBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinSupercharge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace CertifiedInverseKernel

variable (CIK : InfoGeometry.Canonical.CertifiedInverseKernel E)

/-- Black-Book-facing alias for the Drazin regular support `P_D = A * Aᴰ`. -/
@[rep_depth krein]
abbrev drazinSupportBlackBook : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.drazinSpectralProjector CIK

/-- Black-Book-facing alias for the Drazin defect support `Q0 = 1 - P_D`. -/
@[rep_depth krein]
abbrev drazinDefectSupportBlackBook : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.drazinComplementaryProjector CIK

/-- Black-Book-facing alias for the Moore-Penrose range support `P_R`. -/
@[rep_depth krein]
abbrev mpRangeSupportBlackBook : EndH :=
  CIK.mpRangeProjector

/-- Black-Book-facing alias for the Moore-Penrose domain/metric support `P_L`. -/
@[rep_depth krein]
abbrev mpDomainSupportBlackBook : EndH :=
  CIK.metricProjector

/-- Black-Book-facing alias for the Moore-Penrose dilation gap. -/
@[rep_depth krein]
noncomputable abbrev dilationGapBlackBook : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.drazinDilationGap CIK

/-- Black-Book-facing alias for the geometric Cartan grading `Γ_G = P_R - P_L`. -/
@[rep_depth krein]
noncomputable abbrev geometricCartanBlackBook : EndH :=
  CIK.GammaG

/-- Black-Book-facing alias for the algebraic Drazin supercharge. -/
@[rep_depth krein]
noncomputable abbrev drazinSuperchargeBlackBook : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.drazinSupercharge CIK

/-- Black-Book-facing alias for the regular compressed kinetic lane. -/
@[rep_depth krein]
noncomputable abbrev regularKineticBlackBook : EndH :=
  DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian CIK

/-- The defect support is the Drazin complement, not the dilation gap. -/
@[rep_depth krein]
theorem drazinDefectSupportBlackBook_eq_one_sub_drazinSupportBlackBook :
    drazinDefectSupportBlackBook CIK = (1 : EndH) - drazinSupportBlackBook CIK := by
  rfl

/-- The dilation gap is the Moore-Penrose range/domain support mismatch. -/
@[rep_depth krein]
theorem dilationGapBlackBook_eq_half_sub_range_domain :
    dilationGapBlackBook CIK =
      ((2 : ℝ)⁻¹) • (mpRangeSupportBlackBook CIK - mpDomainSupportBlackBook CIK) := by
  rfl

/-- The geometric Cartan grading is twice the dilation gap. -/
@[rep_depth krein]
theorem geometricCartanBlackBook_eq_two_smul_dilationGapBlackBook :
    geometricCartanBlackBook CIK = (2 : ℝ) • dilationGapBlackBook CIK := by
  simpa [geometricCartanBlackBook, dilationGapBlackBook] using
    CIK.GammaG_eq_two_smul_dilationGap

/-- The Drazin commutator with the dilation gap is half the anomaly difference. -/
@[rep_depth krein]
theorem commutator_support_gap_eq_half_sub_anomalies :
    DrazinSupercharge.commutator (drazinSupportBlackBook CIK) (dilationGapBlackBook CIK)
      =
    ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly) := by
  simpa [drazinSupportBlackBook, dilationGapBlackBook] using
    _root_.InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.commutator_drazinSpectralProjector_drazinDilationGap_eq_half_sub_anomalies
      (CIK := CIK)

/-- The Drazin supercharge is the right-left anomaly difference. -/
@[rep_depth krein]
theorem drazinSuperchargeBlackBook_eq_sub_anomalies :
    drazinSuperchargeBlackBook CIK = CIK.rightChiralAnomaly - CIK.chiralAnomaly := by
  simpa [drazinSuperchargeBlackBook] using
    _root_.InfoGeometry.Canonical.DrazinSupercharge.CertifiedInverseKernel.drazinSupercharge_eq_rightChiralAnomaly_sub_chiralAnomaly
      (CIK := CIK)

/-- Equivalent theorem-owned identity `Q_D = 2 • [P_D, G]`. -/
@[rep_depth krein]
theorem drazinSuperchargeBlackBook_eq_two_smul_commutator :
    drazinSuperchargeBlackBook CIK =
      (2 : ℝ) •
        DrazinSupercharge.commutator (drazinSupportBlackBook CIK) (dilationGapBlackBook CIK) := by
  rfl

/-- Equivalent theorem-owned identity `Q_D = [P_D, Γ_G]`. -/
@[rep_depth krein]
theorem drazinSuperchargeBlackBook_eq_commutator_geometricCartan :
    drazinSuperchargeBlackBook CIK =
      DrazinSupercharge.commutator
        (drazinSupportBlackBook CIK) (geometricCartanBlackBook CIK) := by
  calc
    drazinSuperchargeBlackBook CIK
        = DrazinSupercharge.CertifiedInverseKernel.supercharge CIK := by
            simpa [drazinSuperchargeBlackBook] using
              DrazinSupercharge.CertifiedInverseKernel.drazinSupercharge_eq_supercharge
                (CIK := CIK)
    _ =
        DrazinSupercharge.commutator
          (drazinSupportBlackBook CIK) (geometricCartanBlackBook CIK) := by
            simpa [drazinSupportBlackBook, geometricCartanBlackBook] using
              DrazinSupercharge.CertifiedInverseKernel.supercharge_eq_commutator_spectralProjector_GammaG
                (CIK := CIK)

/-- The Drazin supercharge is odd with respect to the spectral grading. -/
@[rep_depth krein]
theorem drazinSuperchargeBlackBook_is_odd :
    DrazinSupercharge.anticommutator
        CIK.toInformationCartanTriple.GammaS (drazinSuperchargeBlackBook CIK) = 0 := by
  simpa [drazinSuperchargeBlackBook] using
    DrazinSupercharge.CertifiedInverseKernel.drazinSupercharge_is_odd (CIK := CIK)

/--
The regular compressed kinetic lane is supported on `P_D`, fixed by the
spectral grading flow, and annihilated by the complementary Drazin support
after transport.
-/
@[rep_depth krein]
theorem regularKineticBlackBook_support_flow_package
    (t : ℝ) :
    (drazinSupportBlackBook CIK * regularKineticBlackBook CIK
        = regularKineticBlackBook CIK)
      ∧ (regularKineticBlackBook CIK * drazinSupportBlackBook CIK
          = regularKineticBlackBook CIK)
      ∧ (CIK.toInformationCartanTriple.spectralAdjointFlow
            CIK.toInformationCartanTriple.GammaS t
            (regularKineticBlackBook CIK)
            = regularKineticBlackBook CIK)
      ∧ (drazinDefectSupportBlackBook CIK
            * CIK.toInformationCartanTriple.spectralAdjointFlow
                CIK.toInformationCartanTriple.GammaS t
                (regularKineticBlackBook CIK) = 0)
      ∧ (CIK.toInformationCartanTriple.spectralAdjointFlow
            CIK.toInformationCartanTriple.GammaS t
            (regularKineticBlackBook CIK)
            * drazinDefectSupportBlackBook CIK = 0) := by
  simpa [drazinSupportBlackBook, drazinDefectSupportBlackBook, regularKineticBlackBook] using
    DrazinSupercharge.CertifiedInverseKernel.regularRestrictedSuperHamiltonian_support_flow_package
      (CIK := CIK) t

end CertifiedInverseKernel

namespace UnifiedSuperchargePackage

open InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
open InfoGeometry.Krein

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH₂" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH₂ := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH₂ :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH₂
local instance : IsTopologicalRing EndH₂ := inferInstance
local instance : CompleteSpace EndH₂ := inferInstance
local instance : SMulCommClass ℝ EndH₂ EndH₂ := inferInstance
local instance : IsScalarTower ℝ EndH₂ EndH₂ := inferInstance

variable (U : UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage (E := E))

/--
Repo-owned odd-odd split for the projected Drazin supercharge:
`{Q_D,Q_D} = 2 • T_D + Z_D`.
-/
@[rep_depth krein]
theorem projectedOddOddBlackBook_eq_two_smul_translation_plus_central :
    DrazinSupercharge.anticommutatorK
        (UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD U)
        (UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.QD U)
      =
    (2 : ℝ) • UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.drazinTranslationCandidate U
      + UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.drazinCentralCandidate U := by
  exact
    UnifiedSuperchargeAlgebra.UnifiedSuperchargePackage.projected_oddOdd_bracket_eq_two_smul_translation_plus_central
      (U := U)

end UnifiedSuperchargePackage

end InfoGeometry.Canonical.DrazinDilationGapBridge
