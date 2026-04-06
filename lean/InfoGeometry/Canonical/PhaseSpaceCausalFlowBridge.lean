import InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
import InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
import InfoGeometry.Canonical.ConformalProjectorCore
import InfoGeometry.Canonical.ChiralCartanCore
import InfoGeometry.Canonical.RelativeModularRecomposition
import InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
import InfoGeometry.Canonical.KKTGeneralizedInverseBridge
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

/-!
# InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge

Causal-flow bridge that packages the upstream generation chain:

owner phase-space seeds → doubled/KKT corridor → conformal and recomposition leaves.

This file is intentionally thin. It reuses the existing owner-to-KKT and
recomposition bridges, then records the paired downstream outputs as a single
causal trunk with two terminal leaves.
-/

namespace InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge

open InfoGeometry.Canonical.PhaseSpaceConformalKKTBridge
open InfoGeometry.Canonical.PhaseSpaceRecompositionBridge
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ChiralCartanCore
open InfoGeometry.Canonical.RelativeModularRecomposition
open InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge
open InfoGeometry.Canonical.KKTGeneralizedInverseBridge
open InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Quantum
open InfoGeometry.Krein

section OwnerToKKT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "H2" => DoubledSpace H
local notation "EndH" => H2 →L[ℝ] H2

/-- The corrected owner phase rotation realizes as the canonical KKT dilation
operator on the doubled split-`Cl(1,1)` carrier. -/
@[rep_depth krein] theorem toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator
    (ρ : H ≃ₗ[ℝ] Module.Dual ℝ H) :
    (toDoubledCopyRho (E := H) ρ).comp (phaseRotation (E := H) ρ)
      = (dilationOperator (E := H)).toLinearMap.comp (toDoubledCopyRho (E := H) ρ) :=
  PhaseSpaceConformalKKTBridge.toDoubledCopyRho_comp_phaseRotation_eq_KKT_dilationOperator
    (H := H) ρ

end OwnerToKKT

section KKTDefects

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Moore-Penrose chiral gap lands in grade zero on the canonical doubled
carrier under the explicit KKT wing hypotheses. -/
@[rep_depth krein] theorem correctedOwner_mpChiralGap_isGZero
    (CIK : CertifiedInverseKernel (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_MP) :
    IsGZero (doubledSpaceCl11Action (E := H)) CIK.mpChiralGap :=
  KKTGeneralizedInverseBridge.mpChiralGap_isGZero
    (X := doubledSpaceCl11Action (E := H)) (CIK := CIK) hA hAMP

/-- The certified dilation gap lands in grade zero on the canonical doubled
carrier under the explicit KKT wing hypotheses. -/
@[rep_depth krein] theorem correctedOwner_dilationGap_isGZero
    (CIK : CertifiedInverseKernel (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_MP) :
    IsGZero (doubledSpaceCl11Action (E := H)) CIK.dilationGap :=
  KKTGeneralizedInverseBridge.dilationGap_isGZero
    (X := doubledSpaceCl11Action (E := H)) (CIK := CIK) hA hAMP

/-- The certified Drazin core projector lands in grade zero on the canonical
doubled carrier under the explicit KKT wing hypotheses. -/
@[rep_depth krein] theorem correctedOwner_drazinCoreProj_isGZero
    (CIK : CertifiedInverseKernel (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
    (hAD : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_D) :
    IsGZero (doubledSpaceCl11Action (E := H)) CIK.drazinCoreProj :=
  KKTGeneralizedInverseBridge.drazinCoreProj_isGZero
    (X := doubledSpaceCl11Action (E := H)) (CIK := CIK) hA hAD

end KKTDefects

section CausalLeaves

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]

/-- The conformal chiral grading leaf is generated in grade zero once the KKT
wing hypotheses hold on the canonical doubled carrier. -/
@[rep_depth krein] theorem correctedOwner_chiralGrading_isGZero
    (CCI : CertifiedConformalInference (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP) :
    IsGZero (doubledSpaceCl11Action (E := H))
      (chiralGrading CCI.toConformalInference) :=
  PhaseSpaceConformalKKTBridge.correctedOwner_chiralGrading_isGZero
    (CCI := CCI) hA hAMP

end CausalLeaves

section RecompositionLeaf

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

/-- The recomposition leaf: the owner-side phase transport descends to the
maintained generalized-metric twist shadow. -/
@[rep_depth projective, simp] theorem phaseTransport_descends_to_generalizedMetricTwistShadow
    (R : PolarizedRecompositionData H α βplus βminus) :
    R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R :=
  PolarizedRecompositionData.phaseTransport_descends_to_generalizedMetricTwistShadow (R := R)

end RecompositionLeaf

section CausalUnification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]
variable {α : Type*} [Fintype α] [Nonempty α]
variable {βplus : Type*} [Fintype βplus] [Nonempty βplus]
variable {βminus : Type*} [Fintype βminus] [Nonempty βminus]

/-- Unification statement: conformal and recomposition leaves are fed by the
same upstream KKT-generated trunk. -/
@[rep_depth krein] theorem correctedOwner_conformal_and_recomposition_leaves
    (CCI : CertifiedConformalInference (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP)
    (R : PolarizedRecompositionData H α βplus βminus) :
    IsGZero (doubledSpaceCl11Action (E := H))
        (chiralGrading CCI.toConformalInference)
      ∧ R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R := by
  refine And.intro ?_ ?_
  · exact correctedOwner_chiralGrading_isGZero (CCI := CCI) hA hAMP
  · exact phaseTransport_descends_to_generalizedMetricTwistShadow (H := H) (R := R)

@[rep_depth krein] theorem correctedOwner_trunk_outputs
    (CIK : CertifiedInverseKernel (DoubledSpace H))
    (CCI : CertifiedConformalInference (DoubledSpace H))
    (hA : IsGOne (doubledSpaceCl11Action (E := H)) CIK.A)
    (hAMP : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_MP)
    (hAD : IsGNegOne (doubledSpaceCl11Action (E := H)) CIK.A_D)
    (hA' : IsGOne (doubledSpaceCl11Action (E := H)) CCI.A)
    (hAMP' : IsGNegOne (doubledSpaceCl11Action (E := H)) CCI.A_MP)
    (R : PolarizedRecompositionData H α βplus βminus) :
    IsGZero (doubledSpaceCl11Action (E := H)) CIK.mpChiralGap
      ∧ IsGZero (doubledSpaceCl11Action (E := H)) CIK.dilationGap
      ∧ IsGZero (doubledSpaceCl11Action (E := H)) CIK.drazinCoreProj
      ∧ IsGZero (doubledSpaceCl11Action (E := H))
          (chiralGrading CCI.toConformalInference)
      ∧ R.couplingLogDefect = PolarizedRecompositionData.generalizedMetricTwistShadow R := by
  refine And.intro ?_ ?_
  · exact correctedOwner_mpChiralGap_isGZero (CIK := CIK) hA hAMP
  · refine And.intro ?_ ?_
    · exact correctedOwner_dilationGap_isGZero (CIK := CIK) hA hAMP
    · refine And.intro ?_ ?_
      · exact correctedOwner_drazinCoreProj_isGZero (CIK := CIK) hA hAD
      · refine And.intro ?_ ?_
        · exact correctedOwner_chiralGrading_isGZero (CCI := CCI) hA' hAMP'
        · exact phaseTransport_descends_to_generalizedMetricTwistShadow (H := H) (R := R)

end CausalUnification

end InfoGeometry.Canonical.PhaseSpaceCausalFlowBridge
