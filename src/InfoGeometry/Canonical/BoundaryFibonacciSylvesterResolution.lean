/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Prescribed boundary/Fibonacci generator defects

The first-generator Sylvester operator is invertible on the actual rectangular
matrix carrier. Two prescribed defects are compatible exactly when the second
is the second-generator defect of the uniquely recovered matrix.
-/

noncomputable section
namespace InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction

local notation "S" => InfoGeometry.Physics.JonesBraidB3.s0
local notation "R" => InfoGeometry.Canonical.YangBaxterProof.R

/-- Cancellation of the mixed terms in the Sylvester equation. -/
theorem firstGeneratorDefect_recovery_identity (T : Matrix (Fin 2) (Fin 8) ℂ) :
    firstGeneratorDefect T * S + R * firstGeneratorDefect T =
      -((R * R + 1) * T) := by
  change (T * S - R * T) * S + R * (T * S - R * T) = _
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
    InfoGeometry.Physics.B3PresentedGroup.s0_sq_eq_neg_one,
    Matrix.mul_neg, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul]
  abel

/-- Explicit solution operator for the first-generator defect. -/
def solveFirstGeneratorDefect (Y : Matrix (Fin 2) (Fin 8) ℂ) :
    Matrix (Fin 2) (Fin 8) ℂ :=
  -((R * R + 1)⁻¹ * (Y * S + R * Y))

theorem solveFirstGeneratorDefect_defect (T : Matrix (Fin 2) (Fin 8) ℂ) :
    solveFirstGeneratorDefect (firstGeneratorDefect T) = T := by
  unfold solveFirstGeneratorDefect
  rw [firstGeneratorDefect_recovery_identity, Matrix.mul_neg, neg_neg,
    ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr obstruction_det_ne_zero),
    Matrix.one_mul]

/-- Every prescribed first-generator defect is attained. -/
theorem firstGeneratorDefect_solve (Y : Matrix (Fin 2) (Fin 8) ℂ) :
    firstGeneratorDefect (solveFirstGeneratorDefect Y) = Y := by
  have hinj : Function.Injective firstGeneratorDefect :=
    LinearMap.ker_eq_bot.mp firstGeneratorDefect_ker_eq_bot
  obtain ⟨T, rfl⟩ := LinearMap.injective_iff_surjective.mp hinj Y
  rw [solveFirstGeneratorDefect_defect]

/-- The explicit recovery is the unique solution, not merely a chosen witness. -/
theorem firstGeneratorDefect_eq_iff (T Y : Matrix (Fin 2) (Fin 8) ℂ) :
    firstGeneratorDefect T = Y ↔ T = solveFirstGeneratorDefect Y := by
  constructor
  · intro h
    rw [← h, solveFirstGeneratorDefect_defect]
  · rintro rfl
    exact firstGeneratorDefect_solve Y

/-- Exact compatibility criterion for both prescribed generator defects. -/
theorem simultaneousGeneratorDefect_solvable_iff
    (Y Z : Matrix (Fin 2) (Fin 8) ℂ) :
    (∃ T, simultaneousGeneratorDefect T = (Y, Z)) ↔
      secondGeneratorDefect (solveFirstGeneratorDefect Y) = Z := by
  constructor
  · rintro ⟨T, hT⟩
    have hfirst : firstGeneratorDefect T = Y := congrArg Prod.fst hT
    have hsecond : secondGeneratorDefect T = Z := congrArg Prod.snd hT
    rw [(firstGeneratorDefect_eq_iff T Y).mp hfirst] at hsecond
    exact hsecond
  · intro h
    exact ⟨solveFirstGeneratorDefect Y, Prod.ext (firstGeneratorDefect_solve Y) h⟩

end InfoGeometry.Canonical.BoundaryFibonacciIntertwinerObstruction
