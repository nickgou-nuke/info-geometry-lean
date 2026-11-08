/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzGNSTensorQuotient
import InfoGeometry.Physics.ComplexStarCuntzRedesign
import InfoGeometry.OperatorAlgebra.CuntzComplexStarProductPositivity

/-!
# Positivity obstruction for the complex-linear tensor-quotient star

The descended `StarRing` operation fixes the image of every complex scalar.
Consequently it cannot support a normalized complex-linear functional that
is nonnegative on every `star x * x`: choosing the scalar `Complex.I` gives
`star x * x = -1`.
-/

namespace InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction

open scoped ComplexOrder
open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.OperatorAlgebra.CuntzComplexStarProductFunctional

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

/-- On the corrected complexified Cuntz carrier, the scalar witness `i` has
star-square `1`. Thus the scalar obstruction above is specific to the
complex-linear star on `CuntzAlg n`; it does not transfer to the conjugate-
semilinear tensor-product star. -/
theorem corrected_complex_scalar_I_star_square (n : ℕ) :
    star (algebraMap ℂ (ComplexStarCuntzAlg (Fin n)) Complex.I) *
        algebraMap ℂ (ComplexStarCuntzAlg (Fin n)) Complex.I = 1 := by
  rw [star_algebraMap_complex, ← map_mul]
  rw [show star Complex.I * Complex.I = (1 : ℂ) by norm_num]
  change (1 : ℂ) ⊗ₜ[ℝ]
      (1 : InfoGeometry.Topology.AlgebraicCuntzQuotient.CuntzAlg ℝ (Fin n)) = 1
  exact Algebra.TensorProduct.one_def.symm

/-- A normalized complex-linear functional therefore evaluates the corrected
scalar `i` star-square at `1`, so this scalar test is compatible with
nonnegativity. No positivity claim on general elements is made. -/
theorem normalized_functional_corrected_scalar_I_nonnegative (n : ℕ)
    (φ : ComplexStarCuntzAlg (Fin n) →ₗ[ℂ] ℂ) (hφ : φ 1 = 1) :
    0 ≤ (φ (star (algebraMap ℂ (ComplexStarCuntzAlg (Fin n)) Complex.I) *
      algebraMap ℂ (ComplexStarCuntzAlg (Fin n)) Complex.I)).re := by
  rw [corrected_complex_scalar_I_star_square]
  rw [hφ]
  norm_num

/-- The corrected binary complex-star Cuntz carrier admits an actual normalized
positive functional on every star-square. This is the operator-algebraic
replacement for the impossible positive functional on the complex-linear
scalar-fixing quotient star above. Positivity is proved on the full quotient,
not just its degree-zero core; no KMS or C*-completion claim is included. -/
theorem corrected_binary_carrier_has_normalized_positive_functional :
    ∃ φ : ComplexStarCuntzAlg Bool →ₗ[ℂ] ℂ,
      φ 1 = 1 ∧ (∀ x, φ (star x) = star (φ x)) ∧
        ∀ x, 0 ≤ φ (star x * x) := by
  let q : Fin 2 → ℝ := fun _ => 1 / 2
  have hq : q 0 + q 1 = 1 := by
    norm_num [q]
  have hpos : ∀ i, 0 ≤ q i := by
    intro i
    norm_num [q]
  exact ⟨quotientProductFunctional q hq,
    quotientProductFunctional_one q hq,
    quotientProductFunctional_star q hq,
    quotientProductFunctional_nonneg q hq hpos⟩

end InfoGeometry.Algebra.CuntzTensorQuotientPositivityObstruction
