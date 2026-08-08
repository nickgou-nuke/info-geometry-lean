import InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge
import InfoGeometry.Canonical.KKTGeneralizedMetricBridge
import InfoGeometry.Canonical.KKTGeneralizedInverseBridge
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.ChiralCartanCore
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge

Adjacency bridge from the corrected phase-space owner lane into the
KKT/generalized-inverse/conformal corridor.

This file stays narrow:

- it uses the corrected phase-space realization into the canonical doubled
  `Cl(1,1)` carrier,
- it reuses the existing KKT grading and generalized-inverse bridge,
- and it packages the resulting grade-zero conformal outputs without adding a
  new ontology layer.
-/

namespace InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge

open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KKTGeneralizedMetricBridge
open InfoGeometry.Canonical.KKTGeneralizedInverseBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ChiralCartanCore
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Quantum
open InfoGeometry.Krein

section OwnerToKKT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => DoubledSpace H
local notation "EndH" => H2 →L[ℝ] H2

/-- The corrected owner `+` phase projector realizes as the canonical KKT `+`
grading projector on the doubled split-`Cl(1,1)` carrier. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_phasePlusProjector_eq_KKT_plusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phasePlusProjector (E := H))
      = (plusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) :=
  toDoubledCopyRho_comp_phasePlusProjector_eq_canonical_plusProjector (H := H) ρ

/-- The corrected owner `-` phase projector realizes as the canonical KKT `-`
grading projector on the doubled split-`Cl(1,1)` carrier. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseMinusProjector_eq_KKT_minusProjector
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseMinusProjector (E := H))
      = (minusProjector (doubledSpaceCl11Action (E := H))).toLinearMap.comp
          (toDoubledCopyRho (E := H) ρ) :=
  toDoubledCopyRho_comp_phaseMinusProjector_eq_canonical_minusProjector (H := H) ρ

/-- The corrected owner Hestenes rotation realizes as the canonical doubled
KKT dilation operator. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
      = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) :=
  toDoubledCopyRho_comp_phaseRotation_eq_dilationOperator (H := H) ρ

end OwnerToKKT

section KKTToConformal

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

/-- On the property conformal surface, the conformal dilation generator is
exactly the property inverse-kernel dilation gap. -/
@[rep_depth krein] theorem CertifiedConformalInference.D_eq_dilationGap
    (CCI : CertifiedConformalInference E) :
    CCI.toConformalInference.D = CCI.toCertifiedInverseKernel.dilationGap := by
  rw [ConformalInference.dilation_eq_half_sub_mp_projectors (CI := CCI.toConformalInference)]
  rfl

section

/-- The conformal chiral grading is exactly twice the property inverse-kernel
dilation gap. -/
@[rep_depth krein] theorem CertifiedConformalInference.chiralGrading_eq_two_smul_dilationGap
    (CCI : CertifiedConformalInference E) :
    chiralGrading CCI.toConformalInference
      = (2 : ℝ) • CCI.toCertifiedInverseKernel.dilationGap := by
  simpa [CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.toInverseKernel', InverseKernel.dilationGap] using
      (InfoGeometry.Canonical.ChiralCartanCore.chiralGrading_eq_two_smul_dilationGap
        (CI := CCI.toConformalInference))

/-- Under the explicit `g₁ / g₋₁` KKT hypotheses, the Moore-Penrose chiral gap
on the property conformal surface lies in grade zero. -/
@[rep_depth krein] theorem CertifiedConformalInference.mpChiralGap_isGZero
    (X : RealSplitCl11Action E)
    (CCI : CertifiedConformalInference E)
    (hA : IsGOne X CCI.A)
    (hAMP : IsGNegOne X CCI.A_MP) :
    IsGZero X CCI.toCertifiedInverseKernel.mpChiralGap :=
  InfoGeometry.Canonical.KKTGeneralizedInverseBridge.mpChiralGap_isGZero
    (X := X) (CIK := CCI.toCertifiedInverseKernel) hA hAMP

/-- Under the explicit `g₁ / g₋₁` KKT hypotheses, the property inverse-kernel
dilation gap on the conformal surface lies in grade zero. -/
@[rep_depth krein] theorem CertifiedConformalInference.dilationGap_isGZero
    (X : RealSplitCl11Action E)
    (CCI : CertifiedConformalInference E)
    (hA : IsGOne X CCI.A)
    (hAMP : IsGNegOne X CCI.A_MP) :
    IsGZero X CCI.toCertifiedInverseKernel.dilationGap :=
  InfoGeometry.Canonical.KKTGeneralizedInverseBridge.dilationGap_isGZero
    (X := X) (CIK := CCI.toCertifiedInverseKernel) hA hAMP

/-- Under the explicit `g₁ / g₋₁` KKT hypotheses, the property Drazin core
projector on the conformal surface lies in grade zero. -/
@[rep_depth krein] theorem CertifiedConformalInference.drazinCoreProj_isGZero
    (X : RealSplitCl11Action E)
    (CCI : CertifiedConformalInference E)
    (hA : IsGOne X CCI.A)
    (hAD : IsGNegOne X CCI.A_D) :
    IsGZero X CCI.toCertifiedInverseKernel.drazinCoreProj :=
  InfoGeometry.Canonical.KKTGeneralizedInverseBridge.drazinCoreProj_isGZero
    (X := X) (CIK := CCI.toCertifiedInverseKernel) hA hAD

end

/-- Under the explicit `g₁ / g₋₁` KKT hypotheses, the conformal dilation
generator itself lies in grade zero. -/
@[rep_depth krein] theorem CertifiedConformalInference.D_isGZero
    (X : RealSplitCl11Action E)
    (CCI : CertifiedConformalInference E)
    (hA : IsGOne X CCI.A)
    (hAMP : IsGNegOne X CCI.A_MP) :
    IsGZero X CCI.toConformalInference.D := by
  rw [CertifiedConformalInference.D_eq_dilationGap (CCI := CCI)]
  exact CertifiedConformalInference.dilationGap_isGZero (X := X) (CCI := CCI) hA hAMP

/-- Under the explicit `g₁ / g₋₁` KKT hypotheses, the conformal chiral grading
is a grade-zero output of the same corrected split-`Cl(1,1)` corridor. -/
@[rep_depth krein] theorem CertifiedConformalInference.chiralGrading_isGZero
    (X : RealSplitCl11Action E)
    (CCI : CertifiedConformalInference E)
    (hA : IsGOne X CCI.A)
    (hAMP : IsGNegOne X CCI.A_MP) :
    IsGZero X (chiralGrading CCI.toConformalInference) := by
  rw [CertifiedConformalInference.chiralGrading_eq_two_smul_dilationGap (CCI := CCI)]
  exact isGZero_smul (X := X) (2 : ℝ)
    (CertifiedConformalInference.dilationGap_isGZero (X := X) (CCI := CCI) hA hAMP)

end KKTToConformal

section CorrectedOwnerEndpoint

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- On the canonical doubled carrier induced from the corrected owner lane, the
conformal chiral grading is grade zero as soon as the explicit KKT wing
hypotheses hold. -/
@[rep_depth krein] theorem correctedOwner_chiralGrading_isGZero
    (CCI : CertifiedConformalInference (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP) :
    IsGZero (doubledSpaceCl11Action (E := H))
      (chiralGrading CCI.toConformalInference) :=
  CertifiedConformalInference.chiralGrading_isGZero
    (X := doubledSpaceCl11Action (E := H)) (CCI := CCI) hA hAMP

end CorrectedOwnerEndpoint

end InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
