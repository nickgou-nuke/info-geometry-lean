import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Projective.ApolloniusNatural
import Mathlib.Tactic

/-!
# Bipolar logarithm as a native SL₂ Cartan parameter

This file recovers the exact finite representation-theoretic content of the
informal "boost plus circular phase" discussion.

It reuses the repository-owned `MatrixStageLorentzKANSoldering` definitions of
`SL₂(ℂ)`, `SU(2)`, the diagonal boost `boostA`, the compact diagonal rotation
`compactK`, Hermitian Minkowski soldering, and the action `X ↦ g X gᴴ`.

The bipolar logarithm supplies only the two real Cartan parameters

`W = eta + i theta`.

No gauge-field, helicity, or dynamical Lorentz claim is added here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarCartanLorentzBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Projective.ApolloniusNatural

/-- Exact reconstruction of a complex number from its real and imaginary parts. -/
theorem bipolarLog_split (s : ℂ) :
    bipolarLog s = (eta s : ℂ) + (theta s : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [eta, theta]

/-- The positive logarithmic half-weight factors into compact phase and positive scale. -/
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
  rw [harg, Complex.exp_add]
  rw [← Complex.ofReal_exp]

/-- The negative logarithmic half-weight carries the opposite compact phase and scale. -/
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
  rw [harg, Complex.exp_add]
  rw [← Complex.ofReal_exp]

/-- The bipolar half-log matrix is exactly the commuting compact/boost Cartan product. -/
theorem halfLogLift_eq_compactK_mul_boostA (s : ℂ) :
    halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, compactK, boostA, Matrix.mul_apply, Fin.sum_univ_two,
      plusWeight_eq_compact_mul_boost, minusWeight_eq_compact_mul_boost]

/-- The bipolar half-log lift is an element of the repository's `SL₂(ℂ)` predicate. -/
theorem halfLogLift_isSL2C (s : ℂ) : isSL2C (halfLogLift s) := by
  exact halfLogLift_det s

/-- Native Hermitian action induced by the bipolar Cartan element. -/
def bipolarSolderingAction (s : ℂ) (X : HermitianMat2) : HermitianMat2 :=
  lorentzSoldering (halfLogLift s) X

/-- The bipolar Cartan action preserves the determinant of every Hermitian block. -/
theorem bipolarSolderingAction_det (s : ℂ) (X : HermitianMat2) :
    (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact lorentzSoldering_isometry (halfLogLift s) (halfLogLift_isSL2C s) X

/-- On the critical line the noncompact Cartan factor disappears exactly. -/
theorem halfLogLift_criticalLine_eq_compactK (y : ℝ) :
    halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) := by
  rw [halfLogLift_eq_compactK_mul_boostA, eta_criticalLine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostA, Matrix.mul_apply, Fin.sum_univ_two]

/-- Consequently the critical-line half-log matrix lies in the native `SU(2)` predicate. -/
theorem halfLogLift_criticalLine_isSU2 (y : ℝ) :
    isSU2 (halfLogLift (criticalLine y)) := by
  rw [halfLogLift_criticalLine_eq_compactK]
  exact compactK_isSU2 _

/-- The canonical projective Apollonius ray reconstructs the same Cayley coordinate. -/
theorem apolloniusRay_bipolar_readout {s : ℂ} (hs : s ∈ punctured01) :
    (apolloniusRay (eta s) (theta s)).1 = crossRatio01 s := by
  simpa [apolloniusRay, mul_comm] using exp_eta_theta hs

/-- Circular/light-cone coordinate carrier for the diagonal Cartan action.
The names are only representation-theoretic readouts of a four-component
complex coordinate tuple. -/
structure CartanCoordinates where
  plus : ℂ
  minus : ℂ
  transversePlus : ℂ
  transverseMinus : ℂ

/-- Exact weight action of the split/compact Cartan parameters. -/
def cartanCoordinateAction (η θ : ℝ) (X : CartanCoordinates) : CartanCoordinates where
  plus := Complex.exp (η : ℂ) * X.plus
  minus := Complex.exp (-(η : ℂ)) * X.minus
  transversePlus := Complex.exp (Complex.I * (θ : ℂ)) * X.transversePlus
  transverseMinus := Complex.exp (-Complex.I * (θ : ℂ)) * X.transverseMinus

/-- Additivity of the two Cartan parameters gives composition of the weight action. -/
theorem cartanCoordinateAction_add
    (η₁ θ₁ η₂ θ₂ : ℝ) (X : CartanCoordinates) :
    cartanCoordinateAction (η₁ + η₂) (θ₁ + θ₂) X =
      cartanCoordinateAction η₁ θ₁ (cartanCoordinateAction η₂ θ₂ X) := by
  cases X
  ext <;> simp [cartanCoordinateAction, Complex.exp_add] <;> ring

/-- Bipolar specialization of the Cartan weight action. -/
def bipolarCoordinateAction (s : ℂ) : CartanCoordinates → CartanCoordinates :=
  cartanCoordinateAction (eta s) (theta s)

/-- On the critical line the split weights are exactly trivial; only the compact
opposite phase weights remain. -/
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
