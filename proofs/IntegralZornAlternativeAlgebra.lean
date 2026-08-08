import proofs.IntegralZornCompositionAlgebra

/-!
# Alternativity and nonassociativity of the integral Zorn algebra

This file records the algebraic properties that distinguish the integral Zorn
composition law from an associative matrix algebra.  The canonical complex
product is proved left- and right-alternative by coordinates; injective scalar
extension descends those identities to the integral algebra.  A concrete
mixed upper/lower-lane witness proves genuine nonassociativity.
-/

noncomputable section

namespace IntegralZornAlternativeAlgebra

set_option maxHeartbeats 1000000

open IntegralZornII44Bridge
open IntegralZornCompositionAlgebra
open CanonicalZornCompositionTriality
open CanonicalZornProjectiveTKKBridge
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornIntegralTrialityEquivariance
open CanonicalZornCliffordRepresentation
open SplitOctonionBraidSU3

/-! ## Canonical alternativity -/

theorem canonicalZorn_left_alternative (X Y : Zorn) :
    zornMul (zornMul X X) Y = zornMul X (zornMul X Y) := by
  apply zorn_ext
  · simp [zornMul, dot3, cross3]
    ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · simp [zornMul, dot3, cross3]
    ring

theorem canonicalZorn_right_alternative (X Y : Zorn) :
    zornMul (zornMul X Y) Y = zornMul X (zornMul Y Y) := by
  apply zorn_ext
  · simp [zornMul, dot3, cross3]
    ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;> simp [zornMul, dot3, cross3] <;> ring
  · simp [zornMul, dot3, cross3]
    ring

theorem canonicalZorn_conj_mul (X Y : Zorn) :
    CanonicalZornCompositionTriality.zornConj (zornMul X Y) =
      zornMul (CanonicalZornCompositionTriality.zornConj Y)
        (CanonicalZornCompositionTriality.zornConj X) := by
  apply zorn_ext
  · simp [CanonicalZornCompositionTriality.zornConj, zornMul, dot3]
    ring
  · funext i
    fin_cases i <;>
      simp [CanonicalZornCompositionTriality.zornConj,
        zornMul, dot3, cross3] <;> ring
  · funext i
    fin_cases i <;>
      simp [CanonicalZornCompositionTriality.zornConj,
        zornMul, dot3, cross3] <;> ring
  · simp [CanonicalZornCompositionTriality.zornConj, zornMul, dot3]
    ring

/-! ## Integral descent -/

theorem integralZorn_left_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X X) Y =
      integralZornMul X (integralZornMul X Y) := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  simp only [integralToCoreZorn_mul, coreToCanonical_mul]
  exact canonicalZorn_left_alternative _ _

theorem integralZorn_right_alternative (X Y : IntegralZorn) :
    integralZornMul (integralZornMul X Y) Y =
      integralZornMul X (integralZornMul Y Y) := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  simp only [integralToCoreZorn_mul, coreToCanonical_mul]
  exact canonicalZorn_right_alternative _ _

theorem integralZornConj_mul (X Y : IntegralZorn) :
    integralZornConj (integralZornMul X Y) =
      integralZornMul (integralZornConj Y) (integralZornConj X) := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  rw [coreToCanonical_integralZornConj,
    coreToCanonical_integralZornMul,
    coreToCanonical_integralZornMul,
    coreToCanonical_integralZornConj,
    coreToCanonical_integralZornConj]
  exact canonicalZorn_conj_mul _ _

/-! ## Explicit nonassociativity witness -/

def integralUpper (u : Fin 3 → ℤ) : IntegralZorn :=
  (0, u, ((fun _ => 0), 0))

def integralLower (v : Fin 3 → ℤ) : IntegralZorn :=
  (0, (fun _ => 0), (v, 0))

def integralE1 : Fin 3 → ℤ := ![1, 0, 0]
def integralE2 : Fin 3 → ℤ := ![0, 1, 0]

def integralAssociator (X Y Z : IntegralZorn) : IntegralZorn :=
  integralZornMul (integralZornMul X Y) Z -
    integralZornMul X (integralZornMul Y Z)

theorem integral_mixed_associator_coordinate :
    (integralAssociator
      (integralUpper integralE1)
      (integralLower integralE1)
      (integralUpper integralE2)).u 1 = 1 := by
  norm_num [integralAssociator, integralUpper, integralLower,
    integralE1, integralE2, integralZornMul, integralDot3,
    integralCross3, IntegralZorn.a, IntegralZorn.u,
    IntegralZorn.v, IntegralZorn.b, Fin.sum_univ_three]
  all_goals rfl

theorem integralZorn_not_associative :
    ∃ X Y Z : IntegralZorn,
      integralZornMul (integralZornMul X Y) Z ≠
        integralZornMul X (integralZornMul Y Z) := by
  refine ⟨integralUpper integralE1, integralLower integralE1,
    integralUpper integralE2, ?_⟩
  intro h
  have hu := congrArg (fun W : IntegralZorn => W.u 1) h
  change
    (integralZornMul
        (integralZornMul (integralUpper integralE1)
          (integralLower integralE1))
        (integralUpper integralE2)).u 1 =
      (integralZornMul (integralUpper integralE1)
        (integralZornMul (integralLower integralE1)
          (integralUpper integralE2))).u 1 at hu
  have ha := integral_mixed_associator_coordinate
  change
    (integralZornMul
        (integralZornMul (integralUpper integralE1)
          (integralLower integralE1))
        (integralUpper integralE2)).u 1 -
      (integralZornMul (integralUpper integralE1)
        (integralZornMul (integralLower integralE1)
          (integralUpper integralE2))).u 1 = 1 at ha
  rw [hu] at ha
  norm_num at ha

/-- The integral split-octonion algebra is unital, composition, alternative,
nonassociative, triality-covariant, five-graded, and projectively closed. -/
theorem integral_octonion_triality_fivegrade_projective_closure
    (X Y : IntegralZorn) (Ψ : DiracSpinor16) :
    integralZornMul X integralZornOne = X ∧
    integralZornMul integralZornOne X = X ∧
    integralZornNorm (integralZornMul X Y) =
      integralZornNorm X * integralZornNorm Y ∧
    integralZornMul (integralZornMul X X) Y =
      integralZornMul X (integralZornMul X Y) ∧
    integralZornMul (integralZornMul X Y) Y =
      integralZornMul X (integralZornMul Y Y) ∧
    (∃ A B C : IntegralZorn,
      integralZornMul (integralZornMul A B) C ≠
        integralZornMul A (integralZornMul B C)) ∧
    integralAxisCycle (integralZornMul X Y) =
      integralZornMul (integralAxisCycle X) (integralAxisCycle Y) ∧
    CanonicalZornCompositionTriality.vectorGradePlus
        (CanonicalZornRealSpin44.realSplit44ToVector8
          (integralZornToRealSplit44 (integralAxisCycle X))) ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.p1 ∧
    ProjectiveAffineConformalClosure55.Q55
      (ProjectiveAffineConformalClosure55.conformalEmbed44to55
        (CanonicalZornRealSpin44.realSplit44ToPAC44
          (integralZornToRealSplit44 (integralAxisCycle X)))) = 0 := by
  exact ⟨integralZornMul_one X, integralZornOne_mul X,
    integralZornNorm_mul X Y, integralZorn_left_alternative X Y,
    integralZorn_right_alternative X Y, integralZorn_not_associative,
    integralAxisCycle_mul X Y,
    (integral_zorn_composition_triality_fivegrade_projective_closure
      X Y Ψ).2.2.2.1,
    (integral_zorn_composition_triality_fivegrade_projective_closure
      X Y Ψ).2.2.2.2⟩

end IntegralZornAlternativeAlgebra

end noncomputable section
