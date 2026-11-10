/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-site exponential Toeplitz kernel and precision matrix

The native `Matrix (Fin 3) (Fin 3)` kernel has entries `α ^ |i-j|`.
Its tridiagonal precision matrix has endpoint diagonal entries `1` and middle
entry `1 + α²`. Both scaled inverse identities hold over any commutative ring.
Over a field, `1 - α² ≠ 0` gives an actual inverse.
The kernel fails to commute with the cyclic shift when `α ≠ α²`, as witnessed
over the rationals at `α = 1/2`; an open Toeplitz kernel is therefore not
automatically a cyclic convolution operator.

This is a finite three-site calculation motivated by the open-boundary kernel
in Karkada et al., arXiv:2602.15029. It does not formalize the continuum
Proposition 3, assert a Fourier basis for an arbitrary Toeplitz matrix, or
remove boundary effects.
-/

namespace InfoGeometry.LLM.LanguageSymmetry

section CommRing

variable {K : Type*} [CommRing K]

/-- The exponential Toeplitz kernel on three consecutive sites. -/
def expToeplitz3 (α : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, α, α ^ 2;
     α, 1, α;
     α ^ 2, α, 1]

/-- Tridiagonal precision numerator, including the endpoint corrections. -/
def tridiagonalPrecision3 (α : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, -α, 0;
     -α, 1 + α ^ 2, -α;
     0, -α, 1]

/-- Cyclic shift of the three coordinate vectors. -/
def cyclicShift3 : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1;
     1, 0, 0;
     0, 1, 0]

/-- Projection onto the first endpoint coordinate of the open chain. -/
def endpointProjection3 : Matrix (Fin 3) (Fin 3) K :=
  !![1, 0, 0;
     0, 0, 0;
     0, 0, 0]

/-- Selecting an endpoint breaks cyclic shift symmetry over any nontrivial
coefficient ring. The `(1,0)` entries of the two products are `0` and `1`. -/
theorem endpointProjection3_not_commute_cyclicShift3 [Nontrivial K] :
    (endpointProjection3 : Matrix (Fin 3) (Fin 3) K) * cyclicShift3 ≠
      cyclicShift3 * endpointProjection3 := by
  intro h
  have h10 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 1 0) h
  simp [endpointProjection3, cyclicShift3, Matrix.mul_apply,
    Fin.sum_univ_succ] at h10

/-- The open-boundary kernel need not have cyclic translation symmetry.
The `(0,0)` entries of the two products are `α` and `α²`, respectively. -/
theorem expToeplitz3_not_commute_cyclicShift3 (α : K) (hα : α ≠ α ^ 2) :
    expToeplitz3 α * cyclicShift3 ≠ cyclicShift3 * expToeplitz3 α := by
  intro h
  apply hα
  have h00 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) h
  simpa [expToeplitz3, cyclicShift3, Matrix.mul_apply, Fin.sum_univ_succ] using h00

/-- Multiplication on the right produces the exact scalar factor. -/
theorem expToeplitz3_mul_precision (α : K) :
    expToeplitz3 α * tridiagonalPrecision3 α =
      (1 - α ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expToeplitz3, tridiagonalPrecision3, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

/-- Multiplication on the left produces the same scalar factor. -/
theorem precision_mul_expToeplitz3 (α : K) :
    tridiagonalPrecision3 α * expToeplitz3 α =
      (1 - α ^ 2) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expToeplitz3, tridiagonalPrecision3, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> ring

end CommRing

/-- A concrete positive decaying kernel that is not cyclically translation invariant. -/
theorem expToeplitz3_half_not_commute_cyclicShift3 :
    expToeplitz3 (1 / 2 : ℚ) * cyclicShift3 ≠
      cyclicShift3 * expToeplitz3 (1 / 2 : ℚ) := by
  apply expToeplitz3_not_commute_cyclicShift3
  norm_num

section Field

variable {K : Type*} [Field K]

/-- The scaled precision matrix is a right inverse away from `α² = 1`. -/
theorem expToeplitz3_mul_scaled_precision (α : K) (hα : 1 - α ^ 2 ≠ 0) :
    expToeplitz3 α * ((1 - α ^ 2)⁻¹ • tridiagonalPrecision3 α) = 1 := by
  rw [Matrix.mul_smul, expToeplitz3_mul_precision, smul_smul,
    inv_mul_cancel₀ hα, one_smul]

/-- The same matrix is a left inverse, with the same necessary scale condition. -/
theorem scaled_precision_mul_expToeplitz3 (α : K) (hα : 1 - α ^ 2 ≠ 0) :
    ((1 - α ^ 2)⁻¹ • tridiagonalPrecision3 α) * expToeplitz3 α = 1 := by
  rw [Matrix.smul_mul, precision_mul_expToeplitz3, smul_smul,
    inv_mul_cancel₀ hα, one_smul]

/-- The actual native nonsingular matrix inverse has the tridiagonal formula. -/
theorem expToeplitz3_inv (α : K) (hα : 1 - α ^ 2 ≠ 0) :
    (expToeplitz3 α)⁻¹ = (1 - α ^ 2)⁻¹ • tridiagonalPrecision3 α :=
  Matrix.inv_eq_left_inv (scaled_precision_mul_expToeplitz3 α hα)

end Field

end InfoGeometry.LLM.LanguageSymmetry
