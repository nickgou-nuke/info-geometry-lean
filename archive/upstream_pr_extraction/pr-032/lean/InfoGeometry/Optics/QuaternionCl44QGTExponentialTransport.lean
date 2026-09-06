import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
import InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance
import InfoGeometry.OperatorAlgebra.NoncommutativeDuhamelDerivative

set_option autoImplicit false

/-!
# Exponential transport for the represented positive Clifford generator

The faithful normed coordinate algebra supports the exact hyperbolic
exponential flow of the represented positive Clifford generator.
Because `coordinateScalarPositiveGenerator ^ 2 = 1`, the one-parameter
flow has the exact closed form `cosh(t) • 1 + sinh(t) • X`.
Inner conjugation by this subgroup is the finite analytic transport
integrating the infinitesimal commutator direction.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44QGTExponentialTransport

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance

/-- The positive Clifford generator squares to identity in the coordinate algebra. -/
@[simp] theorem coordinateScalarPositiveGenerator_sq :
    coordinateScalarPositiveGenerator * coordinateScalarPositiveGenerator = 1 := by
  dsimp [coordinateScalarPositiveGenerator]
  rw [← map_mul, ← doubledInternalOperator_mul,
      scalarPositiveComplexGamma_sq,
      doubledInternalOperator_one,
      map_one]

/-- Exponential of the represented positive Clifford generator in exact closed form. -/
def coordinateCliffordExponential (t : ℂ) : CoordinateContinuousEnd :=
  Complex.cosh t • (1 : CoordinateContinuousEnd) + Complex.sinh t • coordinateScalarPositiveGenerator

@[simp] theorem coordinateCliffordExponential_zero :
    coordinateCliffordExponential 0 = 1 := by
  dsimp [coordinateCliffordExponential]
  rw [Complex.cosh_zero, Complex.sinh_zero]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.one_apply, one_smul, zero_smul, add_zero]

/-- Exponentials of the one-dimensional Clifford line obey the additive
parameter law. -/
theorem coordinateCliffordExponential_add (s t : ℂ) :
    coordinateCliffordExponential (s + t) =
      coordinateCliffordExponential s * coordinateCliffordExponential t := by
  dsimp [coordinateCliffordExponential]
  rw [Complex.cosh_add, Complex.sinh_add]
  have h_sq := coordinateScalarPositiveGenerator_sq
  apply ContinuousLinearMap.ext
  intro v
  have h_prod : coordinateScalarPositiveGenerator (coordinateScalarPositiveGenerator v) = v := by
    calc
      coordinateScalarPositiveGenerator (coordinateScalarPositiveGenerator v)
        = (coordinateScalarPositiveGenerator * coordinateScalarPositiveGenerator) v := rfl
      _ = (1 : CoordinateContinuousEnd) v := by rw [h_sq]
      _ = v := rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
             ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
             map_add, map_smul, h_prod]
  rw [add_smul, add_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  have h1 : Complex.cosh s * Complex.cosh t = Complex.cosh t * Complex.cosh s := mul_comm _ _
  have h2 : Complex.sinh s * Complex.sinh t = Complex.sinh t * Complex.sinh s := mul_comm _ _
  have h3 : Complex.sinh s * Complex.cosh t = Complex.cosh t * Complex.sinh s := mul_comm _ _
  have h4 : Complex.cosh s * Complex.sinh t = Complex.sinh t * Complex.cosh s := mul_comm _ _
  rw [h1, h2, h3, h4]
  abel

/-- Derivative of the exact hyperbolic Clifford exponential. -/
theorem hasDerivAt_coordinateCliffordExponential (t : ℂ) :
    HasDerivAt coordinateCliffordExponential
      (Complex.sinh t • (1 : CoordinateContinuousEnd) +
        Complex.cosh t • coordinateScalarPositiveGenerator) t := by
  simpa only [coordinateCliffordExponential] using
    ((Complex.hasDerivAt_cosh t).smul_const
      (1 : CoordinateContinuousEnd)).add
      ((Complex.hasDerivAt_sinh t).smul_const
        coordinateScalarPositiveGenerator)

theorem hasDerivAt_coordinateCliffordExponential_zero :
    HasDerivAt coordinateCliffordExponential
      coordinateScalarPositiveGenerator 0 := by
  have h := hasDerivAt_coordinateCliffordExponential 0
  rw [Complex.sinh_zero, Complex.cosh_zero] at h
  have h_simp : (0 : ℂ) • (1 : CoordinateContinuousEnd) + (1 : ℂ) • coordinateScalarPositiveGenerator =
      coordinateScalarPositiveGenerator := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [h_simp] at h
  exact h

/-- The exponential equipped with its explicit negative-parameter inverse. -/
def coordinateCliffordExponentialUnit (t : ℂ) : CoordinateContinuousEndˣ where
  val := coordinateCliffordExponential t
  inv := coordinateCliffordExponential (-t)
  val_inv := by
    rw [← coordinateCliffordExponential_add, add_neg_cancel, coordinateCliffordExponential_zero]
  inv_val := by
    rw [← coordinateCliffordExponential_add, neg_add_cancel, coordinateCliffordExponential_zero]

@[simp] theorem coordinateCliffordExponentialUnit_val (t : ℂ) :
    (coordinateCliffordExponentialUnit t : CoordinateContinuousEnd) =
      coordinateCliffordExponential t :=
  rfl

@[simp] theorem coordinateCliffordExponentialUnit_inv_val (t : ℂ) :
    (↑((coordinateCliffordExponentialUnit t)⁻¹) : CoordinateContinuousEnd) =
      coordinateCliffordExponential (-t) :=
  rfl

@[simp] theorem coordinateCliffordExponentialUnit_zero :
    coordinateCliffordExponentialUnit 0 = 1 := by
  apply Units.ext
  simp

theorem coordinateCliffordExponentialUnit_add (s t : ℂ) :
    coordinateCliffordExponentialUnit (s + t) =
      coordinateCliffordExponentialUnit s * coordinateCliffordExponentialUnit t := by
  apply Units.ext
  exact coordinateCliffordExponential_add s t

/-- Finite analytic conjugation flow generated by the positive Clifford
operator. -/
def coordinateCliffordConjugationFlow
    (t : ℂ) (A : CoordinateContinuousEnd) : CoordinateContinuousEnd :=
  innerConjugation (coordinateCliffordExponentialUnit t) A

@[simp] theorem coordinateCliffordConjugationFlow_zero
    (A : CoordinateContinuousEnd) :
    coordinateCliffordConjugationFlow 0 A = A := by
  simp [coordinateCliffordConjugationFlow, innerConjugation]

/-- The conjugation transport is an additive one-parameter group action. -/
theorem coordinateCliffordConjugationFlow_add
    (s t : ℂ) (A : CoordinateContinuousEnd) :
    coordinateCliffordConjugationFlow (s + t) A =
      coordinateCliffordConjugationFlow s
        (coordinateCliffordConjugationFlow t A) := by
  rw [coordinateCliffordConjugationFlow,
    coordinateCliffordExponentialUnit_add]
  exact InfoGeometry.Optics.LocalGaugeFrameComposition.innerConjugation_mul
    (coordinateCliffordExponentialUnit s)
    (coordinateCliffordExponentialUnit t) A

/-- The finite hyperbolic conjugation flow integrates the infinitesimal
positive-Clifford commutator direction. -/
theorem hasDerivAt_coordinateCliffordConjugationFlow_zero
    (A : CoordinateContinuousEnd) :
    HasDerivAt (fun t : ℂ ↦ coordinateCliffordConjugationFlow t A)
      (associativeCommutator coordinateScalarPositiveGenerator A) 0 := by
  have hplus : HasDerivAt
      (fun t : ℂ ↦ coordinateCliffordExponential t * A)
      (coordinateScalarPositiveGenerator * A) 0 :=
    hasDerivAt_coordinateCliffordExponential_zero.mul_const A
  have hminus : HasDerivAt
      (fun t : ℂ ↦ coordinateCliffordExponential (-t))
      (-coordinateScalarPositiveGenerator) 0 := by
    have h1 : HasDerivAt (fun t : ℂ => Complex.cosh (-t)) 0 (0 : ℂ) := by
      simpa [Complex.cosh_neg] using Complex.hasDerivAt_cosh 0
    have h2 : HasDerivAt (fun t : ℂ => Complex.sinh (-t)) (-1) (0 : ℂ) := by
      simpa [Complex.sinh_neg] using (Complex.hasDerivAt_sinh (0 : ℂ)).neg
    have h_add := (h1.smul_const (1 : CoordinateContinuousEnd)).add (h2.smul_const coordinateScalarPositiveGenerator)
    have h_simp : (0 : ℂ) • (1 : CoordinateContinuousEnd) + (-1 : ℂ) • coordinateScalarPositiveGenerator =
        -coordinateScalarPositiveGenerator := by
      apply ContinuousLinearMap.ext; intro v; simp
    rw [h_simp] at h_add
    exact h_add
  have hmul := hplus.mul hminus
  change HasDerivAt
    (fun t : ℂ ↦
      coordinateCliffordExponential t * A *
        coordinateCliffordExponential (-t))
    (associativeCommutator coordinateScalarPositiveGenerator A) 0
  have h_id : coordinateScalarPositiveGenerator * A * coordinateCliffordExponential (-0) +
      coordinateCliffordExponential 0 * A * -coordinateScalarPositiveGenerator =
      associativeCommutator coordinateScalarPositiveGenerator A := by
    rw [neg_zero, coordinateCliffordExponential_zero, mul_one, one_mul]
    dsimp [associativeCommutator]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
               ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply]
    rw [A.map_neg, sub_eq_add_neg]
  rw [h_id] at hmul
  exact hmul

/-- Every analytic coordinate Chern character is exactly conserved along the
positive-Clifford exponential conjugation flow. -/
theorem coordinateFrechetChernCharacter_conjugationFlow
    (k : ℕ) (t : ℂ) (A : CoordinateContinuousEnd) :
    coordinateFrechetChernCharacter k
        (coordinateCliffordConjugationFlow t A) =
      coordinateFrechetChernCharacter k A :=
  coordinateFrechetChernCharacter_innerConjugation
    k (coordinateCliffordExponentialUnit t) A

end InfoGeometry.Optics.QuaternionCl44QGTExponentialTransport
