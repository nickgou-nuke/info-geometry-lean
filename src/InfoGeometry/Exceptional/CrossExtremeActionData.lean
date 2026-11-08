import InfoGeometry.Exceptional.FreudenthalChargeLinear
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

structure CrossExtremeActionData (D : CubicJordanDatum J) where
  gradeEquiv : FreudenthalCharge J ≃ₗ[ℝ] FreudenthalCharge J
  minusAction : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  plusAction : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  bracketMinusPlus : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  bracketPlusMinus : FreudenthalCharge J →ₗ[ℝ] FreudenthalCharge J
  signMinus : ℝ
  signPlus : ℝ
  coefficientMinus : ℝ
  coefficientPlus : ℝ
  scaleWeightMinus2 : ℝ
  scaleWeightMinus1 : ℝ
  scaleWeightZero : ℝ
  scaleWeightPlus1 : ℝ
  scaleWeightPlus2 : ℝ
  bracketMinusPlus_eq :
    bracketMinusPlus = signMinus • (coefficientMinus • minusAction)
  bracketPlusMinus_eq :
    bracketPlusMinus = signPlus • (coefficientPlus • plusAction)
  scaleWeight_zero : scaleWeightZero = 0
  scaleWeight_opposite :
    scaleWeightMinus2 + scaleWeightPlus2 = 0 ∧
      scaleWeightMinus1 + scaleWeightPlus1 = 0
  dualAction_eq :
    plusAction = gradeEquiv.toLinearMap.comp
      (minusAction.comp gradeEquiv.symm.toLinearMap)

structure CrossExtremeOmegaCompatibility
    (E : CrossExtremeActionData D) : Prop where
  minus_preserves : ∀ x y,
    FreudenthalCharge.symplecticForm D (E.minusAction x) (E.minusAction y) =
      FreudenthalCharge.symplecticForm D x y
  plus_preserves : ∀ x y,
    FreudenthalCharge.symplecticForm D (E.plusAction x) (E.plusAction y) =
      FreudenthalCharge.symplecticForm D x y

structure CrossExtremeMixedBracketCompatibility
    (E : CrossExtremeActionData D) : Prop where
  minus_intertwines : ∀ x y z,
    E.minusAction (symplecticRankTwo D x y z) =
      symplecticRankTwo D (E.minusAction x) (E.minusAction y)
        (E.minusAction z)
  plus_intertwines : ∀ x y z,
    E.plusAction (symplecticRankTwo D x y z) =
      symplecticRankTwo D (E.plusAction x) (E.plusAction y)
        (E.plusAction z)

@[simp] theorem CrossExtremeActionData.bracketMinusPlus_apply
    (E : CrossExtremeActionData D) (x : FreudenthalCharge J) :
    E.bracketMinusPlus x =
      E.signMinus • (E.coefficientMinus • E.minusAction x) := by
  rw [E.bracketMinusPlus_eq]
  simp

@[simp] theorem CrossExtremeActionData.bracketPlusMinus_apply
    (E : CrossExtremeActionData D) (x : FreudenthalCharge J) :
    E.bracketPlusMinus x =
      E.signPlus • (E.coefficientPlus • E.plusAction x) := by
  rw [E.bracketPlusMinus_eq]
  simp

end InfoGeometry.Exceptional.Freudenthal
