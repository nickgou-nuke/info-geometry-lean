import proofs.CanonicalZornIntegralSpinRepresentation
import proofs.CanonicalZornTrialitySpinEquivariance

/-!
# Integral Zorn axis triality and Clifford equivariance

The cyclic permutation of the three Zorn axes is internal and must not be
confused with outer Cartan triality.  This file realizes that internal cycle as
an order-three element of `GL₈(ℤ)`, proves compatibility with real and complex
scalar extension, and connects it to the established Clifford/gamma,
five-graded, and affine projective closure.
-/

noncomputable section

namespace CanonicalZornIntegralTrialityEquivariance

open IntegralZornII44Bridge
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornProjectiveTKKBridge
open CanonicalZornRealSpin44
open CanonicalZornIntegralSpinTrialityClosure
open CanonicalZornIntegralSpinRepresentation
open CanonicalZornTrialitySpinEquivariance
open CanonicalZornFiveGradedClosure
open ProjectiveAffineConformalClosure55

/-- Cyclic permutation of the three integral Zorn vector axes. -/
def integralAxisCycleLinear : IntegralZorn →ₗ[ℤ] IntegralZorn where
  toFun X :=
    (X.a, (![X.u 1, X.u 2, X.u 0],
      (![X.v 1, X.v 2, X.v 0], X.b)))
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · apply Prod.ext
        · funext i
          fin_cases i <;> rfl
        · rfl
  map_smul' n X := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · apply Prod.ext
        · funext i
          fin_cases i <;> rfl
        · rfl

theorem integralAxisCycleLinear_order_three (X : IntegralZorn) :
    integralAxisCycleLinear
      (integralAxisCycleLinear (integralAxisCycleLinear X)) = X := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · rfl

/-- The internal axis cycle as an integral linear equivalence. -/
def integralAxisCycle : IntegralZorn ≃ₗ[ℤ] IntegralZorn where
  toFun := integralAxisCycleLinear
  invFun X := integralAxisCycleLinear (integralAxisCycleLinear X)
  left_inv := integralAxisCycleLinear_order_three
  right_inv := integralAxisCycleLinear_order_three
  map_add' := integralAxisCycleLinear.map_add
  map_smul' := integralAxisCycleLinear.map_smul

theorem integralAxisCycle_order_three (X : IntegralZorn) :
    integralAxisCycle (integralAxisCycle (integralAxisCycle X)) = X :=
  integralAxisCycleLinear_order_three X

def integralAxisCycleUnit :
    LinearMap.GeneralLinearGroup ℤ IntegralZorn :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv integralAxisCycle

theorem integralAxisCycleUnit_pow_three : integralAxisCycleUnit ^ 3 = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro X
  exact integralAxisCycle_order_three X

theorem integralAxisCycle_norm (X : IntegralZorn) :
    integralZornNorm (integralAxisCycle X) = integralZornNorm X := by
  simp [integralAxisCycle, integralAxisCycleLinear, integralZornNorm,
    IntegralZorn.a, IntegralZorn.u, IntegralZorn.v, IntegralZorn.b,
    Fin.sum_univ_three]
  ring

/-- The integral axis cycle is exactly real Zorn coordinate triality after
forgetting the lattice. -/
theorem integralToCoreZorn_axisCycle (X : IntegralZorn) :
    integralToCoreZorn (integralAxisCycle X) =
      ZornCore.triality (integralToCoreZorn X) := by
  apply ZornCore.Zorn.ext'
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem coreToCanonical_integralAxisCycle (X : IntegralZorn) :
    coreToCanonical (integralToCoreZorn (integralAxisCycle X)) =
      canonicalTriality (coreToCanonical (integralToCoreZorn X)) := by
  rw [integralToCoreZorn_axisCycle, coreToCanonical_triality]

/-- The `GL₈(ℤ)` cycle scalar-extends to the canonical complex vector-axis
cycle. -/
theorem integralAxisCycle_vector_intertwining (X : IntegralZorn) :
    realSplit44ToVector8
        (integralZornToRealSplit44 (integralAxisCycle X)) =
      vectorAxisCycle
        (realSplit44ToVector8 (integralZornToRealSplit44 X)) := by
  apply ZornCopy.ext
  rw [axisCycleCopy_val]
  rw [realVector_integralZornToRealSplit44,
    realVector_integralZornToRealSplit44]
  exact coreToCanonical_integralAxisCycle X

/-- Integral axis triality, complex Clifford covariance, five-grade placement,
and affine projective closure coexist without identifying the internal cycle
with outer Cartan triality. -/
theorem integral_axis_triality_clifford_fivegrade_projective_closure
    (X : IntegralZorn) (Ψ : DiracSpinor16) :
    integralAxisCycleUnit ^ 3 = 1 ∧
    integralZornNorm (integralAxisCycle X) = integralZornNorm X ∧
    realSplit44ToVector8
        (integralZornToRealSplit44 (integralAxisCycle X)) =
      vectorAxisCycle
        (realSplit44ToVector8 (integralZornToRealSplit44 X)) ∧
    diracAxisCycle
        (diracGamma
          (realSplit44ToVector8 (integralZornToRealSplit44 X)) Ψ) =
      diracGamma
        (realSplit44ToVector8
          (integralZornToRealSplit44 (integralAxisCycle X)))
        (diracAxisCycle Ψ) ∧
    vectorGradePlus
        (realSplit44ToVector8
          (integralZornToRealSplit44 (integralAxisCycle X))) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44
        (integralZornToRealSplit44 (integralAxisCycle X)))) = 0 := by
  refine ⟨integralAxisCycleUnit_pow_three,
    integralAxisCycle_norm X,
    integralAxisCycle_vector_intertwining X, ?_,
    realSplit44_vector_grade_plus _, realSplit44_projective_null _⟩
  rw [integralAxisCycle_vector_intertwining]
  exact diracGamma_axis_covariant _ _

end CanonicalZornIntegralTrialityEquivariance

end noncomputable section
