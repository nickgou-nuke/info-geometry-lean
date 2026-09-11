import InfoGeometry.Exceptional.FreudenthalFiveGradedLieClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Explicit extreme-grade action data

This file records the additional data required before a contact five-graded
bracket can be promoted to a Lie bracket.  It deliberately defines no
canonical action and proves no Jacobi theorem: the two cross-extreme actions,
the lane identification, signs, coefficients, scale weights, and
compatibilities are all explicit inputs.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

structure ExtremeActionData where
  minusAction : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  plusAction : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  minusSign : ℝ
  plusSign : ℝ
  minusCoefficient : ℝ
  plusCoefficient : ℝ
  scaleNormalization : ℝ
  scaleWeightMinus2 : ℝ
  scaleWeightMinus1 : ℝ
  scaleWeightZero : ℝ
  scaleWeightPlus1 : ℝ
  scaleWeightPlus2 : ℝ
  dualLaneIdentification : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J
  dual_lane_action :
    plusAction = dualLaneIdentification.toLinearMap.comp
      (minusAction.comp dualLaneIdentification.symm.toLinearMap)
  scale_weights_sum :
    scaleWeightMinus2 + scaleWeightPlus2 = 0 ∧
    scaleWeightMinus1 + scaleWeightPlus1 = 0
  omega_minus_compatibility : ∀ x y : FreudenthalCharge J,
    FreudenthalCharge.symplecticForm D (minusAction x) (minusAction y) =
      FreudenthalCharge.symplecticForm D x y
  omega_plus_compatibility : ∀ x y : FreudenthalCharge J,
    FreudenthalCharge.symplecticForm D (plusAction x) (plusAction y) =
      FreudenthalCharge.symplecticForm D x y
  mixed_compatibility : ∀ T : SymplecticTKKZero D,
      ∀ x : FreudenthalCharge J,
        minusAction ((T : Module.End ℝ (FreudenthalCharge J)) x) =
          (T : Module.End ℝ (FreudenthalCharge J)) (minusAction x) ∧
        plusAction ((T : Module.End ℝ (FreudenthalCharge J)) x) =
          (T : Module.End ℝ (FreudenthalCharge J)) (plusAction x)

namespace ExtremeActionData

theorem plusAction_apply_via_dual
    (E : ExtremeActionData D) (x : FreudenthalCharge J) :
    E.plusAction x =
      E.dualLaneIdentification
        (E.minusAction (E.dualLaneIdentification.symm x)) := by
  exact LinearMap.congr_fun E.dual_lane_action x

theorem scale_weights_sum_minus
    (E : ExtremeActionData D) :
    E.scaleWeightMinus2 + E.scaleWeightPlus2 = 0 :=
  E.scale_weights_sum.1

theorem scale_weights_sum_plus
    (E : ExtremeActionData D) :
    E.scaleWeightMinus1 + E.scaleWeightPlus1 = 0 :=
  E.scale_weights_sum.2

end ExtremeActionData

/-- Bracket readbacks for a separately supplied corrected bracket. -/
structure CorrectedFiveGradedBracketData
    (E : ExtremeActionData D) where
  bracket : FiveGradedCarrier D → FiveGradedCarrier D → FiveGradedCarrier D
  bracketMinusPlus : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  bracketPlusMinus : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  bracket_minus_plus : ∀ x,
    bracket (genEminus D E.minusCoefficient) (injChargePlus D x) =
      injChargeMinus D (E.minusSign • bracketMinusPlus x)
  bracket_plus_minus : ∀ x,
    bracket (genEplus D E.plusCoefficient) (injChargeMinus D x) =
      injChargePlus D (E.plusSign • bracketPlusMinus x)

namespace CorrectedFiveGradedBracketData

@[simp] theorem bracketMinusPlus_apply
    {E : ExtremeActionData D} (C : CorrectedFiveGradedBracketData D E)
    (x : FreudenthalCharge J) :
    C.bracket (genEminus D E.minusCoefficient) (injChargePlus D x) =
      injChargeMinus D (E.minusSign • C.bracketMinusPlus x) :=
  C.bracket_minus_plus x

@[simp] theorem bracketPlusMinus_apply
    {E : ExtremeActionData D} (C : CorrectedFiveGradedBracketData D E)
    (x : FreudenthalCharge J) :
    C.bracket (genEplus D E.plusCoefficient) (injChargeMinus D x) =
      injChargePlus D (E.plusSign • C.bracketPlusMinus x) :=
  C.bracket_plus_minus x

end CorrectedFiveGradedBracketData

end InfoGeometry.Exceptional.Freudenthal
