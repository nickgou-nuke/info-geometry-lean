import InfoGeometry.Canonical.ZornOperatorGradeReversalContract
import InfoGeometry.Canonical.OperatorZornGaugeCovariance

/-!
# Signed exchange on the unchanged operator-Zorn carrier

A MulEquiv requires multiplication, not associativity. The unsigned sheet
flip's product defect is retained explicitly; no Tomita identification occurs.
-/

namespace InfoGeometry.Canonical.OperatorZornExchangeAutomorphism

open InfoGeometry.Physics.NCG
open OperatorZornFourPotentialGauge OperatorZornGaugeCovariance
open InfoGeometry.Canonical.OperatorZornRealModule

variable {A : Type*} [Ring A]

def exchange (X : OperatorZornMatrix A) : OperatorZornMatrix A :=
  operatorZornCoordinates X.n_minus X.n_plus (-X.sigma_minus) (-X.sigma_plus)

@[simp] theorem exchange_involutive (X : OperatorZornMatrix A) :
    exchange (exchange X) = X := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals simp [exchange, operatorZornCoordinates]

theorem exchange_add (X Y : OperatorZornMatrix A) :
    exchange (X + Y) = exchange X + exchange Y := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    change -(X.sigma_minus i + Y.sigma_minus i) =
      (-X.sigma_minus i) + (-Y.sigma_minus i)
    abel
  · funext i
    change -(X.sigma_plus i + Y.sigma_plus i) =
      (-X.sigma_plus i) + (-Y.sigma_plus i)
    abel

theorem exchange_neg (X : OperatorZornMatrix A) :
    exchange (-X) = -exchange X := by
  apply operatorZornMatrix_ext
  · rfl
  · rfl
  · funext i
    change -(-X.sigma_minus i) = -( -X.sigma_minus i)
    rfl
  · funext i
    change -(-X.sigma_plus i) = -( -X.sigma_plus i)
    rfl

theorem exchange_sub (X Y : OperatorZornMatrix A) :
    exchange (X - Y) = exchange X - exchange Y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, exchange_add, exchange_neg]

theorem exchange_mul (X Y : OperatorZornMatrix A) :
    exchange (X * Y) = exchange X * exchange Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [exchange, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals simp only [smul_eq_mul, sub_eq_add_neg, Pi.neg_apply, neg_one_smul, one_smul,
    neg_mul, mul_neg, neg_neg]
  all_goals abel_nf

def exchangeMulEquiv : OperatorZornMatrix A ≃* OperatorZornMatrix A where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_involutive
  right_inv := exchange_involutive
  map_mul' := exchange_mul

@[simp] theorem exchange_nPlus (a : A) : exchange (nPlus a) = nMinus a := by
  apply operatorZornMatrix_ext
  all_goals first | rfl | (funext i; simp [exchange, nPlus, nMinus, operatorZornCoordinates])

@[simp] theorem exchange_nMinus (a : A) : exchange (nMinus a) = nPlus a := by
  apply operatorZornMatrix_ext
  all_goals first | rfl | (funext i; simp [exchange, nPlus, nMinus, operatorZornCoordinates])

@[simp] theorem exchange_sigmaPlus (u : OperatorVector A) :
    exchange (sigmaPlus u) = sigmaMinus (-u) := by
  apply operatorZornMatrix_ext
  all_goals first | rfl | (funext i; simp [exchange, sigmaPlus, sigmaMinus, operatorZornCoordinates])

@[simp] theorem exchange_sigmaMinus (u : OperatorVector A) :
    exchange (sigmaMinus u) = sigmaPlus (-u) := by
  apply operatorZornMatrix_ext
  all_goals first | rfl | (funext i; simp [exchange, sigmaPlus, sigmaMinus, operatorZornCoordinates])

theorem exchange_associator (X Y Z : OperatorZornMatrix A) :
    exchange (OperatorZornFourPotentialGauge.associator X Y Z) =
      OperatorZornFourPotentialGauge.associator (exchange X) (exchange Y) (exchange Z) := by
  unfold OperatorZornFourPotentialGauge.associator
  simp only [exchange_sub, exchange_mul]

theorem exchange_bracket (X Y : OperatorZornMatrix A) :
    exchange (OperatorZornFourPotentialGauge.bracket X Y) =
      OperatorZornFourPotentialGauge.bracket (exchange X) (exchange Y) := by
  unfold OperatorZornFourPotentialGauge.bracket
  rw [exchange_sub, exchange_mul, exchange_mul]

theorem exchange_coefficientDeriv (p : A) (X : OperatorZornMatrix A) :
    exchange (OperatorZornFourPotentialGauge.coefficientDeriv p X) =
      OperatorZornFourPotentialGauge.coefficientDeriv p (exchange X) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals dsimp [exchange, OperatorZornFourPotentialGauge.coefficientDeriv,
    OperatorZornFourPotentialGauge.coefficientBracket, operatorZornCoordinates]
  all_goals simp only [smul_eq_mul, sub_eq_add_neg, Pi.neg_apply, neg_one_smul,
    neg_mul, mul_neg, neg_neg]
  all_goals abel_nf

end InfoGeometry.Canonical.OperatorZornExchangeAutomorphism
