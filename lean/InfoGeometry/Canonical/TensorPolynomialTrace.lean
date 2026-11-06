/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorExactCurvatureTrace
import InfoGeometry.Canonical.NormalizedTraceCauchySchwarz
import InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialTrace

/-!
# Polynomial graded trace and Cauchy--Schwarz on the actual matrix colimit

This module uses the existing full-matrix algebraic direct limit and its
constructed normalized trace. The polynomial result is valid for arbitrary
limit operators. The inequality is the real tracial Cauchy--Schwarz bound,
proved by a common finite-stage representative, not a statistical
Cramér--Rao theorem or a norm-completion result.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorPolynomialTrace

open Polynomial
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge
open InfoGeometry.Canonical.TensorExactCurvatureTrace
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialTrace

/-- Evaluation of the existing trace agrees with the normalized trace of
each finite representative. -/
@[simp] theorem normalizedTraceLimit_ofStage (n : ℕ) (X : Stage n) :
    normalizedTraceLimit (ofStage n X) = normalizedTrace n X := rfl

/-- The existing linear trace is uniquely determined by all finite-stage
readouts. This does not require it to preserve multiplication. -/
theorem normalizedTraceLimit_unique (τ : Limit →ₗ[ℝ] ℝ)
    (hτ : ∀ n (X : Stage n), τ (ofStage n X) = normalizedTrace n X) :
    τ = normalizedTraceLimit := by
  ext X
  induction X using DirectLimit.induction with
  | _ n X => exact hτ n X

/-- All positive-degree Peirce metric contributions cancel in the actual
colimit trace; a polynomial contributes only its constant coefficient. -/
theorem normalizedTraceLimit_grading_aeval {P : Limit} (hP : P * P = P)
    (A C : Limit) (F : ℝ[X]) :
    normalizedTraceLimit (invS P * aeval (genV P A C) F) =
      F.coeff 0 * normalizedTraceLimit (invS P) := by
  exact cyclic_grading_aeval normalizedTraceLimit normalizedTraceLimit_cyclic hP A C F

/-- The zero-constant-term case requires neither positivity nor division by
two: it is a consequence of cyclicity and the Peirce commutator identity. -/
theorem normalizedTraceLimit_grading_aeval_zero {P : Limit} (hP : P * P = P)
    (A C : Limit) (F : ℝ[X]) (hF : F.coeff 0 = 0) :
    normalizedTraceLimit (invS P * aeval (genV P A C) F) = 0 := by
  rw [normalizedTraceLimit_grading_aeval hP A C F, hF, zero_mul]

/-- Cauchy--Schwarz holds for arbitrary representatives of the full real
matrix algebraic direct limit. -/
theorem normalizedTraceLimit_cauchy_schwarz (X Y : Limit) :
    normalizedTraceLimit (star X * Y) ^ 2 ≤
      normalizedTraceLimit (star X * X) * normalizedTraceLimit (star Y * Y) := by
  induction X, Y using DirectLimit.induction₂ with
  | _ n A B =>
      rw [limit_star_mk, limit_star_mk, DirectLimit.mul_def,
        DirectLimit.mul_def, DirectLimit.mul_def]
      change normalizedTrace n (star A * B) ^ 2 ≤
        normalizedTrace n (star A * A) * normalizedTrace n (star B * B)
      simpa only [normalizedTrace, NormalizedTraceCauchySchwarz.normalizedTrace,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        one_div, div_eq_mul_inv, one_mul, mul_comm] using
        NormalizedTraceCauchySchwarz.normalizedTrace_cauchy_schwarz
          ((2 : ℝ) ^ n) (pow_pos (by norm_num) n) A B

end InfoGeometry.Canonical.TensorPolynomialTrace
