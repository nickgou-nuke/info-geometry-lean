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
  all_goals first | (funext i) | skip
  all_goals dsimp [exchange, operatorZornCoordinates]
  all_goals noncomm_ring

theorem exchange_sub (X Y : OperatorZornMatrix A) :
    exchange (X - Y) = exchange X - exchange Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals dsimp [exchange, operatorZornCoordinates]
  all_goals noncomm_ring

theorem exchange_mul (X Y : OperatorZornMatrix A) :
    exchange (X * Y) = exchange X * exchange Y := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [exchange, operatorZornCoordinates,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

def exchangeMulEquiv : OperatorZornMatrix A ≃* OperatorZornMatrix A where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_involutive
  right_inv := exchange_involutive
  map_mul' := exchange_mul

@[simp] theorem exchange_nPlus (a : A) : exchange (nPlus a) = nMinus a := by
  apply operatorZornMatrix_ext <;> simp [exchange, nPlus, nMinus, operatorZornCoordinates]

@[simp] theorem exchange_nMinus (a : A) : exchange (nMinus a) = nPlus a := by
  apply operatorZornMatrix_ext <;> simp [exchange, nPlus, nMinus, operatorZornCoordinates]

@[simp] theorem exchange_sigmaPlus (u : OperatorVector A) :
    exchange (sigmaPlus u) = sigmaMinus (-u) := by
  apply operatorZornMatrix_ext <;> simp [exchange, sigmaPlus, sigmaMinus, operatorZornCoordinates]

@[simp] theorem exchange_sigmaMinus (u : OperatorVector A) :
    exchange (sigmaMinus u) = sigmaPlus (-u) := by
  apply operatorZornMatrix_ext <;> simp [exchange, sigmaPlus, sigmaMinus, operatorZornCoordinates]

theorem unsigned_flip_product_defect (X Y : OperatorZornMatrix A) :
    zornFlipOperator (X * Y) - zornFlipOperator X * zornFlipOperator Y =
      operatorZornCoordinates 0 0
        (operatorCross X.sigma_plus Y.sigma_plus + operatorCross X.sigma_plus Y.sigma_plus)
        (-(operatorCross X.sigma_minus Y.sigma_minus + operatorCross X.sigma_minus Y.sigma_minus)) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i; fin_cases i) | skip
  all_goals dsimp [zornFlipOperator, operatorZornCoordinates, operatorCross,
    NCZornElement.mul, NCZornElement.zornDot, NCZornElement.zornCross]
  all_goals noncomm_ring

theorem exchange_associator (X Y Z : OperatorZornMatrix A) :
    exchange (associator X Y Z) = associator (exchange X) (exchange Y) (exchange Z) := by
  unfold associator
  simp only [exchange_sub, exchange_mul]

theorem exchange_bracket (X Y : OperatorZornMatrix A) :
    exchange (bracket X Y) = bracket (exchange X) (exchange Y) := by
  unfold bracket
  rw [exchange_sub, exchange_mul, exchange_mul]

theorem exchange_coefficientDeriv (p : A) (X : OperatorZornMatrix A) :
    exchange (coefficientDeriv p X) = coefficientDeriv p (exchange X) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals dsimp [exchange, coefficientDeriv, coefficientBracket, operatorZornCoordinates]
  all_goals noncomm_ring

variable {Direction : Type*}

theorem exchange_covariant (p : Direction → A) (Phi : ConnectionCoefficients Direction A)
    (xi : Direction) (X : OperatorZornMatrix A) :
    exchange (covariant p Phi xi X) =
      covariant p (fun i => exchange (Phi i)) xi (exchange X) := by
  unfold covariant
  rw [exchange_add, exchange_coefficientDeriv, exchange_mul]

theorem exchange_fieldStrength (p : Direction → A) (Phi : ConnectionCoefficients Direction A)
    (xi eta : Direction) :
    exchange (fieldStrength p Phi xi eta) =
      fieldStrength p (fun i => exchange (Phi i)) xi eta := by
  unfold fieldStrength
  simp only [exchange_add, exchange_sub, exchange_coefficientDeriv, exchange_bracket]

theorem exchange_curvatureAction (p : Direction → A) (Phi : ConnectionCoefficients Direction A)
    (xi eta : Direction) (X : OperatorZornMatrix A) :
    exchange (curvatureAction p Phi xi eta X) =
      curvatureAction p (fun i => exchange (Phi i)) xi eta (exchange X) := by
  unfold curvatureAction
  simp only [exchange_sub, exchange_covariant]

theorem exchange_adjointCovariant (p : Direction → A)
    (Phi : ConnectionCoefficients Direction A) (xi : Direction) (X : OperatorZornMatrix A) :
    exchange (adjointCovariant p Phi xi X) =
      adjointCovariant p (fun i => exchange (Phi i)) xi (exchange X) := by
  unfold adjointCovariant
  rw [exchange_add, exchange_coefficientDeriv, exchange_bracket]

theorem exchange_bianchi (p : Direction → A) (Phi : ConnectionCoefficients Direction A)
    (xi eta zeta : Direction) :
    exchange (bianchi p Phi xi eta zeta) =
      bianchi p (fun i => exchange (Phi i)) xi eta zeta := by
  unfold bianchi
  simp only [exchange_add, exchange_adjointCovariant, exchange_fieldStrength]

theorem exchange_gauge (g : Aˣ) (X : OperatorZornMatrix A) :
    exchange (gauge g X) = gauge g (exchange X) := by
  apply operatorZornMatrix_ext
  all_goals first | (funext i) | skip
  all_goals dsimp [exchange, gauge, mapCoefficients,
    OperatorZornRepresentationCurvatureBridge.mapOperatorVector, operatorZornCoordinates,
    coefficientConjugation]
  all_goals noncomm_ring

end InfoGeometry.Canonical.OperatorZornExchangeAutomorphism
