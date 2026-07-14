import IntegralZornBilinearComposition
import CanonicalZornIntegralSpinRepresentation

/-!
# Unified canonical Zorn closure

This module is the final typed dependency capstone for the canonical Zorn
architecture.  It places in one theorem the integral alternative composition
algebra, its arithmetic spin representation, internal axis triality, outer
Cartan triality, Clifford covariance, the five-graded carrier placements, and
the affine conformal projective null lift.

Internal axis triality and outer Cartan triality remain distinct operations;
their simultaneous appearance is not an identification of them.
-/

noncomputable section

namespace CanonicalZornUnifiedClosure

open IntegralZornII44Bridge
open IntegralZornCompositionAlgebra
open IntegralZornAlternativeAlgebra
open IntegralZornBilinearComposition
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornProjectiveTKKBridge
open CanonicalZornRealSpin44
open CanonicalZornRealComplexSpinBaseChange
open CanonicalZornRealSpinTrialityClosure
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornIntegralSpinSubgroup
open CanonicalZornIntegralSpinRepresentation
open CanonicalZornIntegralTrialityEquivariance
open CanonicalZornTrialitySpinEquivariance
open CanonicalZornOuterTrialityGroup
open CanonicalZornFiveGradedClosure
open ProjectiveAffineConformalClosure55

/-- Complete compiler-checked closure of the integral/canonical Zorn,
octonionic, spin, triality, five-graded, and affine projective layers. -/
theorem canonical_zorn_unified_closure
    (g : integralSpin44) (X Y : IntegralZorn)
    (S : SpinorPlus8) (C : SpinorMinus8) (Ψ : DiracSpinor16) :
    integralZornCompositionLaws.mul X Y = integralZornMul X Y ∧
    integralZornNorm (integralZornCompositionLaws.mul X Y) =
      integralZornNorm X * integralZornNorm Y ∧
    integralZornCompositionLaws.mul
        (integralZornCompositionLaws.mul X X) Y =
      integralZornCompositionLaws.mul X
        (integralZornCompositionLaws.mul X Y) ∧
    integralZornCompositionLaws.mul
        (integralZornCompositionLaws.mul X Y) Y =
      integralZornCompositionLaws.mul X
        (integralZornCompositionLaws.mul Y Y) ∧
    (∃ A B D : IntegralZorn,
      integralZornCompositionLaws.mul
          (integralZornCompositionLaws.mul A B) D ≠
        integralZornCompositionLaws.mul A
          (integralZornCompositionLaws.mul B D)) ∧
    integralZornToRealSplit44
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      realSpinVectorLinear g.1 (integralZornToRealSplit44 X) ∧
    integralZornNorm
        ((integralSpinRepresentation g : Module.End ℤ IntegralZorn) X) =
      integralZornNorm X ∧
    integralAxisCycleUnit ^ 3 = 1 ∧
    integralAxisCycle (integralZornCompositionLaws.mul X Y) =
      integralZornCompositionLaws.mul
        (integralAxisCycle X) (integralAxisCycle Y) ∧
    diracAxisCycle
        (diracGamma (realSplit44ToVector8
          (integralZornToRealSplit44 X)) Ψ) =
      diracGamma (realSplit44ToVector8
        (integralZornToRealSplit44 (integralAxisCycle X)))
        (diracAxisCycle Ψ) ∧
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv
            (realLocusSpinRelatedRepresentation
              (realSpinToRealLocusSpin g.1)))) =
      realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1) ∧
    relatedVectorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1))
        (realSplit44ToVector8 (integralZornToRealSplit44 X)) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1)) S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1)) C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44
        (realSpinVectorLinear g.1 (integralZornToRealSplit44 X)))) = 0 := by
  have hspin := realSpin44_affine_projective_triality_closure
    g.1 (integralZornToRealSplit44 X) S C
  have haxis :=
    integral_axis_triality_clifford_fivegrade_projective_closure X Ψ
  exact ⟨rfl,
    integralZornCompositionLaws.norm_mul X Y,
    integralZornCompositionLaws.left_alternative X Y,
    integralZornCompositionLaws.right_alternative X Y,
    integralZornCompositionLaws.nonassociative,
    integralSpinRepresentation_real_intertwining g X,
    integralSpinRepresentation_preserves_norm g X,
    integralAxisCycleUnit_pow_three,
    integralZornCompositionLaws.triality_mul X Y,
    haxis.2.2.2.1,
    hspin.1, hspin.2.1, hspin.2.2.1, hspin.2.2.2.1,
    hspin.2.2.2.2.2⟩

end CanonicalZornUnifiedClosure

end noncomputable section
