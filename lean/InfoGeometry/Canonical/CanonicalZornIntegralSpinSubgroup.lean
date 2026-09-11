import InfoGeometry.Canonical.CanonicalZornIntegralSpinTrialityClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The integral-lattice-preserving real spin subgroup

The full real split `Spin(4,4)` action on the diagonal quadratic carrier need
not preserve the embedded integral Zorn lattice. This file isolates the honest
arithmetic subgroup by requiring preservation of that lattice in both forward
and inverse directions, then packages its induced action and the resulting
triality/five-grade/projective closure statement.
-/

noncomputable section

namespace CanonicalZornIntegralSpinSubgroup

open IntegralZornII44Bridge
open CanonicalZornProjectiveTKKBridge
open CanonicalZornCompositionTriality
open CanonicalZornRealSpin44
open CanonicalZornRealComplexSpinBaseChange
open CanonicalZornRealSpinTrialityClosure
open CanonicalZornIntegralSpinTrialityClosure

 theorem realSpinVectorLinear_one : realSpinVectorLinear 1 = 1 := by
  apply LinearMap.ext
  intro x
  change realSpinVectorLinear 1 x = x
  rw [← realSpinToRealLocusSpin_vector_action, map_one,
    realLocusVectorAction_one]

theorem realSpinVectorLinear_mul
    (g h : spinGroup realQuadratic44) :
    realSpinVectorLinear (g * h) =
      realSpinVectorLinear g * realSpinVectorLinear h := by
  apply LinearMap.ext
  intro x
  rw [← realSpinToRealLocusSpin_vector_action,
    map_mul, realLocusVectorAction_mul,
    realSpinToRealLocusSpin_vector_action,
    realSpinToRealLocusSpin_vector_action]
  rfl

theorem realSpinVectorLinear_inv_apply
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    realSpinVectorLinear g⁻¹ (realSpinVectorLinear g x) = x := by
  calc
    realSpinVectorLinear g⁻¹ (realSpinVectorLinear g x) =
        (realSpinVectorLinear g⁻¹ * realSpinVectorLinear g) x := rfl
    _ = realSpinVectorLinear (g⁻¹ * g) x := by
      rw [realSpinVectorLinear_mul]
    _ = x := by
      rw [inv_mul_cancel, realSpinVectorLinear_one]
      rfl

theorem integralZornToRealSplit44_injective :
    Function.Injective integralZornToRealSplit44 := by
  intro X Y h
  apply integralToCoreZorn_injective
  have hp := congrArg realSplit44ToPAC44 h
  rw [realSplit44ToPAC44_integralZornToRealSplit44,
    realSplit44ToPAC44_integralZornToRealSplit44] at hp
  simpa only [pac44ToCoreZorn_coreZornToPAC44] using
    congrArg pac44ToCoreZorn hp

/-- A real spin element preserves the embedded integral Zorn lattice both
forward and backward. -/
def PreservesIntegralZornLattice
    (g : spinGroup realQuadratic44) : Prop :=
  (∀ X : IntegralZorn, ∃ Y : IntegralZorn,
    realSpinVectorLinear g (integralZornToRealSplit44 X) =
      integralZornToRealSplit44 Y) ∧
  (∀ X : IntegralZorn, ∃ Y : IntegralZorn,
    realSpinVectorLinear g⁻¹ (integralZornToRealSplit44 X) =
      integralZornToRealSplit44 Y)

theorem preservesIntegralZornLattice_one :
    PreservesIntegralZornLattice 1 := by
  constructor <;> intro X <;> refine ⟨X, ?_⟩
  · rw [realSpinVectorLinear_one]
    rfl
  · rw [inv_one, realSpinVectorLinear_one]
    rfl

theorem preservesIntegralZornLattice_mul
    {g h : spinGroup realQuadratic44}
    (hg : PreservesIntegralZornLattice g)
    (hh : PreservesIntegralZornLattice h) :
    PreservesIntegralZornLattice (g * h) := by
  constructor
  · intro X
    obtain ⟨Y, hY⟩ := hh.1 X
    obtain ⟨Z, hZ⟩ := hg.1 Y
    refine ⟨Z, ?_⟩
    rw [LinearMap.congr_fun (realSpinVectorLinear_mul g h)]
    change realSpinVectorLinear g
      (realSpinVectorLinear h (integralZornToRealSplit44 X)) = _
    rw [hY, hZ]
  · intro X
    obtain ⟨Y, hY⟩ := hg.2 X
    obtain ⟨Z, hZ⟩ := hh.2 Y
    refine ⟨Z, ?_⟩
    rw [mul_inv_rev,
      LinearMap.congr_fun (realSpinVectorLinear_mul h⁻¹ g⁻¹)]
    change realSpinVectorLinear h⁻¹
      (realSpinVectorLinear g⁻¹ (integralZornToRealSplit44 X)) = _
    rw [hY, hZ]

theorem preservesIntegralZornLattice_inv
    {g : spinGroup realQuadratic44}
    (hg : PreservesIntegralZornLattice g) :
    PreservesIntegralZornLattice g⁻¹ := by
  constructor
  · exact hg.2
  · simpa only [inv_inv] using hg.1

/-- Arithmetic subgroup of real `Spin(4,4)` preserving the integral Zorn
lattice. -/
def integralSpin44 : Subgroup (spinGroup realQuadratic44) where
  carrier := {g | PreservesIntegralZornLattice g}
  one_mem' := preservesIntegralZornLattice_one
  mul_mem' hg hh := preservesIntegralZornLattice_mul hg hh
  inv_mem' hg := preservesIntegralZornLattice_inv hg

/-- Integral image point selected from the forward preservation certificate. -/
def integralSpinAction (g : integralSpin44) (X : IntegralZorn) : IntegralZorn :=
  Classical.choose (g.2.1 X)

theorem integralSpinAction_spec (g : integralSpin44) (X : IntegralZorn) :
    realSpinVectorLinear g.1 (integralZornToRealSplit44 X) =
      integralZornToRealSplit44 (integralSpinAction g X) :=
  Classical.choose_spec (g.2.1 X)

theorem integralSpinAction_one (X : IntegralZorn) :
    integralSpinAction 1 X = X := by
  apply integralZornToRealSplit44_injective
  rw [← integralSpinAction_spec]
  change realSpinVectorLinear (1 : spinGroup realQuadratic44)
    (integralZornToRealSplit44 X) = integralZornToRealSplit44 X
  rw [realSpinVectorLinear_one]
  rfl

theorem integralSpinAction_mul
    (g h : integralSpin44) (X : IntegralZorn) :
    integralSpinAction (g * h) X =
      integralSpinAction g (integralSpinAction h X) := by
  apply integralZornToRealSplit44_injective
  rw [← integralSpinAction_spec, ← integralSpinAction_spec,
    ← integralSpinAction_spec]
  exact LinearMap.congr_fun (realSpinVectorLinear_mul g.1 h.1)
    (integralZornToRealSplit44 X)

theorem realSpinVectorLinear_preserves_quadratic
    (g : spinGroup realQuadratic44) (x : RealSplit44) :
    realQuadratic44 (realSpinVectorLinear g x) = realQuadratic44 x := by
  exact (realSpin44_affine_projective_triality_closure g x 0 0).2.2.2.2.1

/-- The arithmetic spin action preserves the integral Zorn norm. -/
theorem integralSpinAction_preserves_norm
    (g : integralSpin44) (X : IntegralZorn) :
    integralZornNorm (integralSpinAction g X) = integralZornNorm X := by
  have hq := realSpinVectorLinear_preserves_quadratic g.1
    (integralZornToRealSplit44 X)
  rw [integralSpinAction_spec,
    realQuadratic44_integralZornToRealSplit44,
    realQuadratic44_integralZornToRealSplit44] at hq
  exact_mod_cast hq

/-- Arithmetic capstone: the selected integral action is a group action,
preserves the `II₄,₄` norm, and its transformed point enters the already proved
Zorn/triality/five-grade/projective closure. -/
theorem integralSpin44_arithmetic_triality_projective_closure
    (g : integralSpin44) (X Y : IntegralZorn)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    integralZornNorm (integralSpinAction g X) = integralZornNorm X ∧
    ii44Quadratic (integralZornToII44 (integralSpinAction g X)) =
      integralZornNorm X ∧
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn (integralSpinAction g X))) =
      (integralZornNorm X : ℂ) ∧
    CanonicalZornProjectiveTKKBridge.coreToCanonical
        (ZornCore.triality
          (integralToCoreZorn (integralSpinAction g X))) =
      CanonicalZornProjectiveTKKBridge.canonicalTriality
        (CanonicalZornProjectiveTKKBridge.coreToCanonical
          (integralToCoreZorn (integralSpinAction g X))) ∧
    CanonicalZornOuterTrialityGroup.cartanTrialityOuterEquiv
        (CanonicalZornOuterTrialityGroup.cartanTrialityOuterEquiv
          (CanonicalZornOuterTrialityGroup.cartanTrialityOuterEquiv
            (realLocusSpinRelatedRepresentation
              (realSpinToRealLocusSpin g.1)))) =
      realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1) ∧
    CanonicalZornOuterTrialityGroup.relatedVectorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1))
        (realSplit44ToVector8 (integralZornToRealSplit44 X)) ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.p1 ∧
    CanonicalZornOuterTrialityGroup.relatedSpinorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1)) S ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.p1 ∧
    CanonicalZornOuterTrialityGroup.relatedSpinorGradeMinus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g.1)) C ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.m1 ∧
    ProjectiveAffineConformalClosure55.Q55
      (ProjectiveAffineConformalClosure55.conformalEmbed44to55
        (realSplit44ToPAC44
          (realSpinVectorLinear g.1
            (integralZornToRealSplit44 X)))) = 0 := by
  have hnorm := integralSpinAction_preserves_norm g X
  have hclosure := integral_spin44_triality_fivegrade_projective_closure
    g.1 X Y S C
  refine ⟨hnorm, ?_, ?_, ?_, hclosure.2.2.2.2.1,
    hclosure.2.2.2.2.2.1, hclosure.2.2.2.2.2.2.1,
    hclosure.2.2.2.2.2.2.2.1, ?_⟩
  · rw [ii44Quadratic_integralZornToII44, hnorm]
  · rw [(integral_ii44_real_complex_norm_bridge
      (integralSpinAction g X)).2.2, hnorm]
  · exact integral_coreToCanonical_triality (integralSpinAction g X)
  · exact (realSpin44_affine_projective_triality_closure
      g.1 (integralZornToRealSplit44 X) S C).2.2.2.2.2

end CanonicalZornIntegralSpinSubgroup

end noncomputable section
