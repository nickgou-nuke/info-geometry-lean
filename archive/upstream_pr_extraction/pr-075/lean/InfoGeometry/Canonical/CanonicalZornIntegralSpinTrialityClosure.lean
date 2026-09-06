import InfoGeometry.Canonical.IntegralZornII44Bridge
import InfoGeometry.Canonical.CanonicalZornRealComplexSpinBaseChange

/-!
# Integral Zorn, real spin, triality, and projective closure

This file joins two previously independent endpoints. Integral Zorn
coordinates already realize the four-hyperbolic-plane quadratic lattice, while
the canonical real `Spin(4,4)` action already reaches the Zorn triality,
five-graded, and affine conformal projective layers. The coordinate map below
identifies their real quadratic carriers and makes that dependency explicit.

No assertion is made that an arbitrary real spin element preserves the
integral lattice. The result is a scalar-extension and quadratic-geometry
bridge, not an arithmetic spin-group theorem.
-/

noncomputable section

namespace CanonicalZornIntegralSpinTrialityClosure

open IntegralZornII44Bridge
open CanonicalZornProjectiveTKKBridge
open CanonicalZornCompositionTriality
open CanonicalZornRealSpin44
open CanonicalZornRealComplexSpinBaseChange
open CanonicalZornRealSpinTrialityClosure
open CanonicalZornOuterTrialityGroup
open CanonicalZornFiveGradedClosure
open ProjectiveAffineConformalClosure55

/-- Forget the integral structure and express an integral Zorn matrix in the
diagonal real split `(4,4)` coordinates used by the Clifford construction. -/
def integralZornToRealSplit44 (X : IntegralZorn) : RealSplit44 :=
  let p := coreZornToPAC44 (integralToCoreZorn X)
  (![p.x0, p.x1, p.x2, p.x3], ![p.y0, p.y1, p.y2, p.y3])

theorem realSplit44ToPAC44_integralZornToRealSplit44 (X : IntegralZorn) :
    realSplit44ToPAC44 (integralZornToRealSplit44 X) =
      coreZornToPAC44 (integralToCoreZorn X) := by
  simp [integralZornToRealSplit44, realSplit44ToPAC44]

/-- The diagonal real quadratic form is the scalar extension of the integral
Zorn norm. -/
theorem realQuadratic44_integralZornToRealSplit44 (X : IntegralZorn) :
    realQuadratic44 (integralZornToRealSplit44 X) =
      (integralZornNorm X : ℝ) := by
  rw [← Q44_realSplit44ToPAC44,
    realSplit44ToPAC44_integralZornToRealSplit44,
    coreZornToPAC44_Q44, integralToCoreZorn_det]

/-- The canonical typed Zorn vector obtained through the real split carrier is
the same coordinatewise complexification used by the integral norm bridge. -/
theorem realVector_integralZornToRealSplit44 (X : IntegralZorn) :
    (realSplit44ToVector8 (integralZornToRealSplit44 X)).val =
      coreToCanonical (integralToCoreZorn X) := by
  rw [realSplit44ToVector8_eq_canonical]
  rw [realSplit44ToPAC44_integralZornToRealSplit44,
    pac44ToCoreZorn_coreZornToPAC44]
  rfl

/-- Integral inputs enter the same nonassociative canonical Zorn product used
by the triality and Clifford layers. -/
theorem integral_coreToCanonical_mul (X Y : IntegralZorn) :
    coreToCanonical (integralToCoreZorn X * integralToCoreZorn Y) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (coreToCanonical (integralToCoreZorn X))
        (coreToCanonical (integralToCoreZorn Y)) :=
  coreToCanonical_mul _ _

/-- Cyclic coordinate triality commutes with the integral-to-real-to-complex
route after the integral coordinates have entered the real Zorn algebra. -/
theorem integral_coreToCanonical_triality (X : IntegralZorn) :
    coreToCanonical (ZornCore.triality (integralToCoreZorn X)) =
      canonicalTriality (coreToCanonical (integralToCoreZorn X)) :=
  coreToCanonical_triality _

/-- The integral `II₄,₄` norm, canonical Zorn multiplication and triality,
Mathlib real spin action, Cartan triality, five grades, and affine conformal
projective null closure coexist in one compiler-checked statement. -/
theorem integral_spin44_triality_fivegrade_projective_closure
    (g : spinGroup realQuadratic44) (X Y : IntegralZorn)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    ii44Quadratic (integralZornToII44 X) = integralZornNorm X ∧
    InfoGeometry.Physics.SplitOctonionBraidSU3.zornNorm
        (coreToCanonical (integralToCoreZorn X)) =
      (integralZornNorm X : ℂ) ∧
    coreToCanonical (integralToCoreZorn X * integralToCoreZorn Y) =
      InfoGeometry.Physics.SplitOctonionBraidSU3.zornMul
        (coreToCanonical (integralToCoreZorn X))
        (coreToCanonical (integralToCoreZorn Y)) ∧
    coreToCanonical (ZornCore.triality (integralToCoreZorn X)) =
      canonicalTriality (coreToCanonical (integralToCoreZorn X)) ∧
    cartanTrialityOuterEquiv
        (cartanTrialityOuterEquiv
          (cartanTrialityOuterEquiv
            (realLocusSpinRelatedRepresentation
              (realSpinToRealLocusSpin g)))) =
      realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g) ∧
    relatedVectorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g))
        (realSplit44ToVector8 (integralZornToRealSplit44 X)) ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradePlus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g)) S ∈
      conformalGrade TKKJordanPairData.TKKGrade.p1 ∧
    relatedSpinorGradeMinus
        (realLocusSpinRelatedRepresentation (realSpinToRealLocusSpin g)) C ∈
      conformalGrade TKKJordanPairData.TKKGrade.m1 ∧
    realQuadratic44
        (realSpinVectorLinear g (integralZornToRealSplit44 X)) =
      (integralZornNorm X : ℝ) ∧
    Q55 (conformalEmbed44to55
      (realSplit44ToPAC44
        (realSpinVectorLinear g (integralZornToRealSplit44 X)))) = 0 := by
  have hspin := realSpin44_affine_projective_triality_closure
    g (integralZornToRealSplit44 X) S C
  exact ⟨ii44Quadratic_integralZornToII44 X,
    (integral_ii44_real_complex_norm_bridge X).2.2,
    integral_coreToCanonical_mul X Y,
    integral_coreToCanonical_triality X,
    hspin.1, hspin.2.1, hspin.2.2.1, hspin.2.2.2.1,
    hspin.2.2.2.2.1.trans
      (realQuadratic44_integralZornToRealSplit44 X),
    hspin.2.2.2.2.2⟩

end CanonicalZornIntegralSpinTrialityClosure

end noncomputable section
