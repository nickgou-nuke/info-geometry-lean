import InfoGeometry.Canonical.IntegralZornII44Bridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.IntegralZornCompositionAlgebra
import InfoGeometry.Canonical.IntegralZornAlternativeAlgebra
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Canonical.CanonicalZornIntegralTrialityEquivariance
import InfoGeometry.Canonical.CanonicalZornIntegralSpinTrialityClosure
import InfoGeometry.Canonical.CanonicalZornCompositionFiveGradeBridge
import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation

/-!
# Bilinear integral Zorn composition package

`IntegralZorn` is a nested product type and therefore inherits an unrelated
componentwise `Mul` instance. The split-octonion product is intentionally kept
as the explicit operation `integralZornMul`. This file proves that operation
is `ℤ`-bilinear, bundles it as a bilinear map, and packages the verified
composition/alternative/triality laws without installing a misleading global
multiplication instance.
-/

noncomputable section

namespace IntegralZornBilinearComposition

open IntegralZornII44Bridge
open IntegralZornCompositionAlgebra
open InfoGeometry.Canonical.IntegralZornAlternativeAlgebra
open CanonicalZornProjectiveTKKBridge
open CanonicalZornIntegralTrialityEquivariance
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornCompositionFiveGradeBridge
open CanonicalZornCliffordRepresentation
open InfoGeometry.Physics.SplitOctonionBraidSU3

theorem integralToCanonical_add (X Y : IntegralZorn) :
    coreToCanonical (integralToCoreZorn (X + Y)) =
      zornAdd (coreToCanonical (integralToCoreZorn X))
        (coreToCanonical (integralToCoreZorn Y)) := by
  apply zorn_ext
  · simp [coreToCanonical, integralToCoreZorn, zornAdd, IntegralZorn.a]
  · funext i
    simp [coreToCanonical, integralToCoreZorn, zornAdd, IntegralZorn.u]
  · funext i
    simp [coreToCanonical, integralToCoreZorn, zornAdd, IntegralZorn.v]
  · simp [coreToCanonical, integralToCoreZorn, zornAdd, IntegralZorn.b]

theorem integralToCanonical_smul (n : ℤ) (X : IntegralZorn) :
    coreToCanonical (integralToCoreZorn (n • X)) =
      zornSmul (n : ℂ) (coreToCanonical (integralToCoreZorn X)) := by
  apply zorn_ext
  · simp [coreToCanonical, integralToCoreZorn, zornSmul, IntegralZorn.a]
  · funext i
    simp [coreToCanonical, integralToCoreZorn, zornSmul, IntegralZorn.u]
  · funext i
    simp [coreToCanonical, integralToCoreZorn, zornSmul, IntegralZorn.v]
  · simp [coreToCanonical, integralToCoreZorn, zornSmul, IntegralZorn.b]

theorem integralZornMul_add_right (X Y Z : IntegralZorn) :
    integralZornMul X (Y + Z) =
      integralZornMul X Y + integralZornMul X Z := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  rw [integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCanonical_add,
    integralToCanonical_add,
    integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCoreZorn_mul, coreToCanonical_mul]
  exact zornMul_add _ _ _

theorem integralZornMul_add_left (X Y Z : IntegralZorn) :
    integralZornMul (X + Y) Z =
      integralZornMul X Z + integralZornMul Y Z := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  rw [integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCanonical_add,
    integralToCanonical_add,
    integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCoreZorn_mul, coreToCanonical_mul]
  exact add_zornMul _ _ _

theorem integralZornMul_smul_right
    (n : ℤ) (X Y : IntegralZorn) :
    integralZornMul X (n • Y) = n • integralZornMul X Y := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  rw [integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCanonical_smul, integralToCanonical_smul,
    integralToCoreZorn_mul, coreToCanonical_mul]
  exact zornMul_smul _ _ _

theorem integralZornMul_smul_left
    (n : ℤ) (X Y : IntegralZorn) :
    integralZornMul (n • X) Y = n • integralZornMul X Y := by
  apply integralToCoreZorn_injective
  apply coreToCanonical_injective
  rw [integralToCoreZorn_mul, coreToCanonical_mul,
    integralToCanonical_smul, integralToCanonical_smul,
    integralToCoreZorn_mul, coreToCanonical_mul]
  exact smul_zornMul _ _ _

/-- The integral split-octonion product as a bilinear map. -/
def integralZornMulBilinear :
    IntegralZorn →ₗ[ℤ] IntegralZorn →ₗ[ℤ] IntegralZorn where
  toFun X :=
    { toFun := integralZornMul X
      map_add' := integralZornMul_add_right X
      map_smul' := fun n Y => integralZornMul_smul_right n X Y }
  map_add' X Y := by
    apply LinearMap.ext
    exact integralZornMul_add_left X Y
  map_smul' n X := by
    apply LinearMap.ext
    exact integralZornMul_smul_left n X

@[simp] theorem integralZornMulBilinear_apply (X Y : IntegralZorn) :
    integralZornMulBilinear X Y = integralZornMul X Y := rfl

/-- A compact law package for the explicitly named integral Zorn product. -/
structure IntegralZornCompositionLaws where
  mul : IntegralZorn →ₗ[ℤ] IntegralZorn →ₗ[ℤ] IntegralZorn
  one : IntegralZorn
  left_one : ∀ X, mul one X = X
  right_one : ∀ X, mul X one = X
  norm_mul : ∀ X Y,
    integralZornNorm (mul X Y) = integralZornNorm X * integralZornNorm Y
  left_alternative : ∀ X Y, mul (mul X X) Y = mul X (mul X Y)
  right_alternative : ∀ X Y, mul (mul X Y) Y = mul X (mul Y Y)
  nonassociative : ∃ X Y Z,
    mul (mul X Y) Z ≠ mul X (mul Y Z)
  conjugation_reverses : ∀ X Y,
    integralZornConj (mul X Y) =
      mul (integralZornConj Y) (integralZornConj X)
  triality_mul : ∀ X Y,
    integralAxisCycle (mul X Y) =
      mul (integralAxisCycle X) (integralAxisCycle Y)

def integralZornCompositionLaws : IntegralZornCompositionLaws where
  mul := integralZornMulBilinear
  one := integralZornOne
  left_one := integralZornOne_mul
  right_one := integralZornMul_one
  norm_mul := integralZornNorm_mul
  left_alternative := integralZorn_left_alternative
  right_alternative := integralZorn_right_alternative
  nonassociative := integralZorn_not_associative
  conjugation_reverses := integralZornConj_mul
  triality_mul := integralAxisCycle_mul

/-- The bilinear composition package remains connected to the five-graded and
affine conformal projective closure. -/
theorem integral_bilinear_octonion_fivegrade_projective_closure
    (X Y : IntegralZorn) (Ψ : DiracSpinor16) :
    integralZornCompositionLaws.mul X Y = integralZornMul X Y ∧
    integralZornNorm (integralZornCompositionLaws.mul X Y) =
      integralZornNorm X * integralZornNorm Y ∧
    integralAxisCycle (integralZornCompositionLaws.mul X Y) =
      integralZornCompositionLaws.mul
        (integralAxisCycle X) (integralAxisCycle Y) ∧
    vectorGradePlus
        (CanonicalZornRealSpin44.realSplit44ToVector8
          (integralZornToRealSplit44 (integralAxisCycle X))) ∈
      CanonicalZornFiveGradedClosure.conformalGrade
        TKKJordanPairData.TKKGrade.p1 ∧
    ProjectiveAffineConformalClosure55.Q55
      (ProjectiveAffineConformalClosure55.conformalEmbed44to55
        (CanonicalZornRealSpin44.realSplit44ToPAC44
          (integralZornToRealSplit44 (integralAxisCycle X)))) = 0 := by
  have h := integral_zorn_composition_triality_fivegrade_projective_closure X Y Ψ
  exact ⟨rfl, integralZornCompositionLaws.norm_mul X Y,
    integralZornCompositionLaws.triality_mul X Y, h.2.2.2.1, h.2.2.2.2⟩

end IntegralZornBilinearComposition

end noncomputable section
