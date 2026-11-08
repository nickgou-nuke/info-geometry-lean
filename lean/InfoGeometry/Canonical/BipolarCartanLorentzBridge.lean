import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Projective.ApolloniusNatural
import Mathlib.Tactic

noncomputable section
namespace InfoGeometry.Canonical.BipolarCartanLorentzBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Projective.ApolloniusNatural

theorem bipolarLog_split (s : ℂ) :
    bipolarLog s = (eta s : ℂ) + (theta s : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [eta, theta]

theorem halfLogLift_eq_compactK_mul_boostA (s : ℂ) :
    halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) := by
  have hp : plusWeight s =
      Complex.exp (Complex.I * ((theta s / 2 : ℝ) : ℂ)) *
        (Real.exp (eta s / 2) : ℂ) := by
    rw [plusWeight, bipolarLog_split]
    have harg :
        ((eta s : ℂ) + (theta s : ℂ) * Complex.I) / 2 =
          Complex.I * ((theta s / 2 : ℝ) : ℂ) + ((eta s / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  have hm : minusWeight s =
      Complex.exp (-Complex.I * ((theta s / 2 : ℝ) : ℂ)) *
        (Real.exp (-(eta s / 2)) : ℂ) := by
    rw [minusWeight, bipolarLog_split]
    have harg :
        -((eta s : ℂ) + (theta s : ℂ) * Complex.I) / 2 =
          -Complex.I * ((theta s / 2 : ℝ) : ℂ) + ((-(eta s / 2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, compactK, boostA, Matrix.mul_apply, Fin.sum_univ_two,
      hp, hm]

theorem halfLogLift_isSL2C (s : ℂ) : isSL2C (halfLogLift s) := by
  exact halfLogLift_det s

def bipolarSolderingAction (s : ℂ) (X : HermitianMat2) : HermitianMat2 :=
  lorentzSoldering (halfLogLift s) X

theorem bipolarSolderingAction_det (s : ℂ) (X : HermitianMat2) :
    (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact lorentzSoldering_isometry (halfLogLift s) (halfLogLift_isSL2C s) X

theorem halfLogLift_criticalLine_eq_compactK (y : ℝ) :
    halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) := by
  rw [halfLogLift_eq_compactK_mul_boostA, eta_criticalLine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostA, Matrix.mul_apply, Fin.sum_univ_two]

theorem halfLogLift_criticalLine_isSU2 (y : ℝ) :
    isSU2 (halfLogLift (criticalLine y)) := by
  rw [halfLogLift_criticalLine_eq_compactK]
  exact compactK_isSU2 _

theorem plusWeight_eq_compact_mul_boost (s : ℂ) :
    plusWeight s =
      Complex.exp (Complex.I * ((theta s / 2 : ℝ) : ℂ)) *
        (Real.exp (eta s / 2) : ℂ) := by
  rw [plusWeight, bipolarLog_split]
  have harg :
      ((eta s : ℂ) + (theta s : ℂ) * Complex.I) / 2 =
        Complex.I * ((theta s / 2 : ℝ) : ℂ) + ((eta s / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]

theorem minusWeight_eq_compact_mul_boost (s : ℂ) :
    minusWeight s =
      Complex.exp (-Complex.I * ((theta s / 2 : ℝ) : ℂ)) *
        (Real.exp (-(eta s / 2)) : ℂ) := by
  rw [minusWeight, bipolarLog_split]
  have harg :
      -((eta s : ℂ) + (theta s : ℂ) * Complex.I) / 2 =
        -Complex.I * ((theta s / 2 : ℝ) : ℂ) + ((-(eta s / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]

theorem apolloniusRay_bipolar_readout {s : ℂ} (hs : s ∈ punctured01) :
    (apolloniusRay (eta s) (theta s)).1 = crossRatio01 s := by
  simpa [apolloniusRay, mul_comm] using exp_eta_theta hs

structure CartanCoordinates where
  plus : ℂ
  minus : ℂ
  transversePlus : ℂ
  transverseMinus : ℂ

@[ext] theorem CartanCoordinates.ext {X Y : CartanCoordinates}
    (hplus : X.plus = Y.plus) (hminus : X.minus = Y.minus)
    (htransversePlus : X.transversePlus = Y.transversePlus)
    (htransverseMinus : X.transverseMinus = Y.transverseMinus) : X = Y := by
  cases X
  cases Y
  simp_all

def cartanCoordinateAction (η θ : ℝ) (X : CartanCoordinates) : CartanCoordinates where
  plus := Complex.exp (η : ℂ) * X.plus
  minus := Complex.exp (-(η : ℂ)) * X.minus
  transversePlus := Complex.exp (Complex.I * (θ : ℂ)) * X.transversePlus
  transverseMinus := Complex.exp (-Complex.I * (θ : ℂ)) * X.transverseMinus

theorem cartanCoordinateAction_add
    (η₁ θ₁ η₂ θ₂ : ℝ) (X : CartanCoordinates) :
    cartanCoordinateAction (η₁ + η₂) (θ₁ + θ₂) X =
      cartanCoordinateAction η₁ θ₁ (cartanCoordinateAction η₂ θ₂ X) := by
  cases X
  apply CartanCoordinates.ext <;> simp only [cartanCoordinateAction]
  · push_cast
    rw [Complex.exp_add]
    ring
  · push_cast
    rw [show -((η₁ : ℂ) + (η₂ : ℂ)) =
        -(η₁ : ℂ) + -(η₂ : ℂ) by ring, Complex.exp_add]
    ring
  · push_cast
    rw [show Complex.I * ((θ₁ : ℂ) + (θ₂ : ℂ)) =
        Complex.I * (θ₁ : ℂ) + Complex.I * (θ₂ : ℂ) by ring,
      Complex.exp_add]
    ring
  · push_cast
    rw [show -Complex.I * ((θ₁ : ℂ) + (θ₂ : ℂ)) =
        -(Complex.I * (θ₁ : ℂ)) + -(Complex.I * (θ₂ : ℂ)) by ring,
      Complex.exp_add]
    ring

def bipolarCoordinateAction (s : ℂ) : CartanCoordinates → CartanCoordinates :=
  cartanCoordinateAction (eta s) (theta s)

theorem bipolarCoordinateAction_criticalLine (y : ℝ) (X : CartanCoordinates) :
    bipolarCoordinateAction (criticalLine y) X =
      { plus := X.plus
        minus := X.minus
        transversePlus :=
          Complex.exp (Complex.I * (theta (criticalLine y) : ℂ)) * X.transversePlus
        transverseMinus :=
          Complex.exp (-Complex.I * (theta (criticalLine y) : ℂ)) * X.transverseMinus } := by
  simp [bipolarCoordinateAction, cartanCoordinateAction, eta_criticalLine]

end InfoGeometry.Canonical.BipolarCartanLorentzBridge
