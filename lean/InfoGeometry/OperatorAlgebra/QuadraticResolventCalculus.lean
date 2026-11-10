/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativePowerDerivative
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Abel

/-!
# Native differentials of a quadratic operator resolvent

The carrier is an arbitrary complete normed algebra over a nontrivially normed
field.  The reciprocal is Mathlib's `Ring.inverse`, and differentiability is
asserted only where the quadratic denominator is a unit.

The existing noncommutative power derivative supplies the square differential
`Φ * H + H * Φ`.  Composing it with the derivative of inversion gives the full
ordered differential of `(1 + s • Φ²)⁻¹ * Φ`; no commutation between the base
point and tangent direction is assumed.

This is a differential of a rational operator map.  It does not identify that
map with the derivative of an operator logarithm, a Legendre transform, or a
Kubo--Mori inverse.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.QuadraticResolventCalculus

open scoped RightActions

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A]

/-- The native insertion differential at degree two retains both orders. -/
theorem powerDerivative_two_apply (Φ H : A) :
    powerDerivative (𝕜 := 𝕜) 2 Φ H = Φ * H + H * Φ := by
  simp [powerDerivative, Finset.sum_range_succ, smul_eq_mul]

/-- The existing power-map theorem specialized to the actual square map. -/
theorem hasFDerivAt_square (Φ : A) :
    HasFDerivAt (fun X : A => X * X)
      (powerDerivative (𝕜 := 𝕜) 2 Φ) Φ := by
  simpa only [pow_two] using
    hasFDerivAt_power_noncommutative (𝕜 := 𝕜) 2 Φ

/-- The arbitrary-direction square differential as the native `fderiv`. -/
theorem fderiv_square_apply (Φ H : A) :
    fderiv 𝕜 (fun X : A => X * X) Φ H = Φ * H + H * Φ := by
  rw [(hasFDerivAt_square (𝕜 := 𝕜) Φ).fderiv]
  exact powerDerivative_two_apply Φ H

/-- The exact error in replacing the insertion differential by twice left
multiplication is the commutator in the displayed orientation. -/
theorem square_differential_left_multiplication_defect (Φ H : A) :
    fderiv 𝕜 (fun X : A => X * X) Φ H - (2 : ℕ) • (Φ * H) =
      H * Φ - Φ * H := by
  rw [fderiv_square_apply, two_nsmul]
  abel

/-- Twice left multiplication is the square differential precisely in
directions commuting with the base point. -/
theorem square_differential_eq_twice_left_iff (Φ H : A) :
    fderiv 𝕜 (fun X : A => X * X) Φ H = (2 : ℕ) • (Φ * H) ↔
      Commute Φ H := by
  rw [fderiv_square_apply, two_nsmul]
  change Φ * H + H * Φ = Φ * H + Φ * H ↔ Φ * H = H * Φ
  exact add_left_cancel_iff.trans eq_comm

/-- The quadratic resolvent, totalized by the native ring inverse.
Derivative theorems below impose the unit-domain hypothesis explicitly. -/
def quadraticResolvent (s : 𝕜) (Φ : A) : A :=
  Ring.inverse (1 + s • (Φ * Φ))

/-- The resolvent coordinate retains its operator factor on the right. -/
def resolventCoordinate (s : 𝕜) (Φ : A) : A :=
  quadraticResolvent s Φ * Φ

/-- Multiplication by the genuine inverse preserves the zero locus. This
uses the unit domain but needs no completeness or differential calculus. -/
theorem resolventCoordinate_eq_zero_iff (s : 𝕜) (Φ : A)
    (hunit : IsUnit (1 + s • (Φ * Φ))) :
    resolventCoordinate s Φ = 0 ↔ Φ = 0 := by
  constructor
  · intro h
    have hi := Ring.mul_inverse_cancel (1 + s • (Φ * Φ)) hunit
    have hmul := congrArg (fun Z : A => (1 + s • (Φ * Φ)) * Z) h
    simpa only [resolventCoordinate, quadraticResolvent, ← mul_assoc,
      hi, one_mul, mul_zero] using hmul
  · rintro rfl
    simp only [resolventCoordinate, mul_zero]

/-- Composition of the native inverse and square differentials. -/
def quadraticResolventDerivative (s : 𝕜) (Φ : A) : A →L[𝕜] A :=
  (-ContinuousLinearMap.mulLeftRight 𝕜 A
    (quadraticResolvent s Φ) (quadraticResolvent s Φ)).comp
      (s • powerDerivative (𝕜 := 𝕜) 2 Φ)

/-- The noncommutative product rule for the resolvent coordinate. -/
def resolventCoordinateDerivative (s : 𝕜) (Φ : A) : A →L[𝕜] A :=
  quadraticResolvent s Φ • ContinuousLinearMap.id 𝕜 A +
    MulOpposite.op Φ • quadraticResolventDerivative s Φ

/-- Explicit arbitrary-direction differential of the quadratic resolvent. -/
theorem quadraticResolventDerivative_apply (s : 𝕜) (Φ H : A) :
    quadraticResolventDerivative s Φ H =
      -(s • (quadraticResolvent s Φ * (Φ * H + H * Φ) *
        quadraticResolvent s Φ)) := by
  change -(quadraticResolvent s Φ *
    (s • powerDerivative (𝕜 := 𝕜) 2 Φ H) * quadraticResolvent s Φ) = _
  rw [powerDerivative_two_apply, mul_smul_comm, smul_mul_assoc]

/-- Explicit arbitrary-direction differential of the resolvent coordinate.
The tangent insertion remains between its two resolvent factors. -/
theorem resolventCoordinateDerivative_apply (s : 𝕜) (Φ H : A) :
    resolventCoordinateDerivative s Φ H =
      quadraticResolvent s Φ * H -
        s • (quadraticResolvent s Φ * (Φ * H + H * Φ) *
          quadraticResolvent s Φ * Φ) := by
  change quadraticResolvent s Φ * H +
    quadraticResolventDerivative s Φ H * Φ = _
  rw [quadraticResolventDerivative_apply, neg_mul, smul_mul_assoc,
    sub_eq_add_neg]

variable [CompleteSpace A]

/-- Native Fréchet differentiability of the quadratic resolvent at every
point where its denominator is a unit. -/
theorem hasFDerivAt_quadraticResolvent (s : 𝕜) (Φ : A)
    (hunit : IsUnit (1 + s • (Φ * Φ))) :
    HasFDerivAt (quadraticResolvent s)
      (quadraticResolventDerivative s Φ) Φ := by
  have hden : HasFDerivAt (fun X : A => 1 + s • (X * X))
      (s • powerDerivative (𝕜 := 𝕜) 2 Φ) Φ :=
    ((hasFDerivAt_square (𝕜 := 𝕜) Φ).const_smul s).const_add 1
  have hinv : HasFDerivAt (Ring.inverse : A → A)
      (-ContinuousLinearMap.mulLeftRight 𝕜 A
        (quadraticResolvent s Φ) (quadraticResolvent s Φ))
      (1 + s • (Φ * Φ)) := by
    obtain ⟨u, hu⟩ := hunit
    simp only [quadraticResolvent, ← hu, Ring.inverse_unit]
    exact hasFDerivAt_ringInverse (𝕜 := 𝕜) u
  exact hinv.comp Φ hden

/-- Native Fréchet differentiability of the resolvent coordinate. -/
theorem hasFDerivAt_resolventCoordinate (s : 𝕜) (Φ : A)
    (hunit : IsUnit (1 + s • (Φ * Φ))) :
    HasFDerivAt (resolventCoordinate s)
      (resolventCoordinateDerivative s Φ) Φ := by
  exact (hasFDerivAt_quadraticResolvent s Φ hunit).mul'
    (hasFDerivAt_id Φ)

/-- The actual Fréchet derivative, applied to any operator direction. -/
theorem fderiv_quadraticResolvent_apply (s : 𝕜) (Φ H : A)
    (hunit : IsUnit (1 + s • (Φ * Φ))) :
    fderiv 𝕜 (quadraticResolvent s) Φ H =
      -(s • (quadraticResolvent s Φ * (Φ * H + H * Φ) *
        quadraticResolvent s Φ)) := by
  rw [(hasFDerivAt_quadraticResolvent s Φ hunit).fderiv]
  exact quadraticResolventDerivative_apply s Φ H

/-- The actual coordinate derivative, with all multiplication order visible. -/
theorem fderiv_resolventCoordinate_apply (s : 𝕜) (Φ H : A)
    (hunit : IsUnit (1 + s • (Φ * Φ))) :
    fderiv 𝕜 (resolventCoordinate s) Φ H =
      quadraticResolvent s Φ * H -
        s • (quadraticResolvent s Φ * (Φ * H + H * Φ) *
          quadraticResolvent s Φ * Φ) := by
  rw [(hasFDerivAt_resolventCoordinate s Φ hunit).fderiv]
  exact resolventCoordinateDerivative_apply s Φ H

end InfoGeometry.OperatorAlgebra.QuadraticResolventCalculus

end
