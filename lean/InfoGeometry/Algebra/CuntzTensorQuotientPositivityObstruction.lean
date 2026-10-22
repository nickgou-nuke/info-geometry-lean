/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzGNSTensorQuotient

/-!
# Positivity obstruction for the complex-linear tensor-quotient star

The descended `StarRing` operation fixes the image of every complex scalar.
Consequently it cannot support a normalized complex-linear functional that
is nonnegative on every `star x * x`: choosing the scalar `Complex.I` gives
`star x * x = -1`.
-/

namespace InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction

open InfoGeometry.Algebra.CuntzTensorQuotient

private theorem quotient_star_fixes_scalar (n : ℕ) (c : ℂ) :
    star (algebraMap ℂ (CuntzAlg n) c) = algebraMap ℂ (CuntzAlg n) c := by
  calc
    star (algebraMap ℂ (CuntzAlg n) c) =
        star (cuntzMk n (algebraMap ℂ (CuntzTensor n) c)) := by
          rw [(cuntzMk n).commutes c]
    _ = cuntzMk n (star (algebraMap ℂ (CuntzTensor n) c)) := by
          rw [star_cuntzMk]
    _ = cuntzMk n (algebraMap ℂ (CuntzTensor n) c) := by
          change cuntzMk n
            (dagger n (algebraMap ℂ (CuntzTensor n) c)) = _
          rw [dagger_algebraMap]
    _ = algebraMap ℂ (CuntzAlg n) c := (cuntzMk n).commutes c

private theorem normalized_linearMap_scalar_readout (n : ℕ)
    (φ : CuntzAlg n →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) (c : ℂ) :
    φ (algebraMap ℂ (CuntzAlg n) c) = c := by
  simpa [Algebra.smul_def, hφ] using (map_smul φ c (1 : CuntzAlg n))

/-- No normalized complex-linear functional on the quotient is positive on
all expressions `star x * x` for its current `StarRing` structure. -/
theorem no_normalized_positive_complexLinearFunctional (n : ℕ) :
    ¬ ∃ φ : CuntzAlg n →ₗ[ℂ] ℂ,
      φ 1 = 1 ∧ ∀ x : CuntzAlg n, 0 ≤ (φ (star x * x)).re := by
  rintro ⟨φ, hφ, hpos⟩
  let x : CuntzAlg n := algebraMap ℂ (CuntzAlg n) Complex.I
  have hsquare : star x * x = algebraMap ℂ (CuntzAlg n) (-1 : ℂ) := by
    dsimp [x]
    calc
      star (algebraMap ℂ (CuntzAlg n) Complex.I) *
          algebraMap ℂ (CuntzAlg n) Complex.I =
        algebraMap ℂ (CuntzAlg n) Complex.I *
          algebraMap ℂ (CuntzAlg n) Complex.I := by
            rw [quotient_star_fixes_scalar]
      _ = algebraMap ℂ (CuntzAlg n) (Complex.I * Complex.I) := by
            rw [← map_mul]
      _ = algebraMap ℂ (CuntzAlg n) (-1 : ℂ) := by
            rw [Complex.I_mul_I]
  have hvalue : φ (star x * x) = (-1 : ℂ) := by
    rw [hsquare]
    exact normalized_linearMap_scalar_readout n φ hφ (-1)
  have hreal : (φ (star x * x)).re = -1 := by
    rw [hvalue]
    norm_num
  have hcontradiction := hpos x
  rw [hreal] at hcontradiction
  norm_num at hcontradiction

/-- The `CuntzGNSState` packet cannot be inhabited because its normalized
linear functional and positivity fields already contradict the quotient's
scalar-fixing star. -/
theorem no_nonempty_CuntzGNSState (n : ℕ) :
    ¬ Nonempty (InfoGeometry.Algebra.CuntzGNSTensorQuotient.CuntzGNSState n) := by
  rintro ⟨F⟩
  exact no_normalized_positive_complexLinearFunctional n
    ⟨F.toLinearMap, F.normalized, F.positive⟩

end InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction
