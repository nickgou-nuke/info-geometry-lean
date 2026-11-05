/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SchurIdempotencyDefect
import InfoGeometry.OperatorAlgebra.DyadicSchurDescent
import Mathlib.Logic.Function.Iterate

/-!
# Noncommuting witnesses and boundaries for Schur defect descent

The coefficient witnesses live in the full matrix ring `M₂(ℤ)`, so their
two-by-two block matrices retain four-by-four operator content. The examples
separate admissible Schur descent from existence of a pivot and from automatic
defect repair. Every finite arithmetic check is kernel checked with `decide`.
-/

namespace InfoGeometry.OperatorAlgebra.SchurDefectExamples

open Matrix InfoGeometry.Core.IdempotencyDefect

/-- A genuine block idempotent with noncommuting, nonzero couplings and a
nonzero ordered correction. Its Schur tail is zero. -/
theorem noncommuting_idempotent_schur_witness :
    ∃ a b c d r : Matrix (Fin 2) (Fin 2) ℤ,
      a * r = 1 ∧ r * a = 1 ∧
      IsIdempotentElem (!![a, b; c, d] :
        Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)) ∧
      b * c ≠ c * b ∧ c * r * b ≠ 0 ∧ d - c * r * b = 0 := by
  refine ⟨1, !![0, 1; 0, 0], !![1, 0; 0, 0], !![0, 1; 0, 0], 1, ?_⟩
  simp only [IsIdempotentElem]
  decide

/-- Even noncommuting nonzero couplings can have a zero ordered Schur
correction. Nonvanishing cannot be inferred from their individual values. -/
theorem noncommuting_nonzero_couplings_zero_correction :
    ∃ b c : Matrix (Fin 2) (Fin 2) ℤ,
      b ≠ 0 ∧ c ≠ 0 ∧ b * c ≠ c * b ∧ c * (1 : Matrix (Fin 2) (Fin 2) ℤ) * b = 0 := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  decide

/-- An invertible full matrix can have a zero, nonunit selected head. -/
theorem invertible_matrix_zero_head :
    ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      M * M = 1 ∧ M 0 0 = 0 ∧ ¬ IsUnit (M 0 0) := by
  refine ⟨!![0, 1; 1, 0], ?_, rfl, ?_⟩
  · decide
  · exact not_isUnit_zero

/-- A three-state strictly lower triangular matrix need not be
square-zero. Its nilpotency index is exactly three. -/
theorem strictly_lower_shift_index_three :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ,
      (∀ i j, i ≤ j → M i j = 0) ∧ M * M ≠ 0 ∧ M * M * M = 0 := by
  refine ⟨!![0, 0, 0; 1, 0, 0; 0, 1, 0], ?_⟩
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
  · decide

/-- A noncentral, nondiagonal operator can be a nonzero fixed point of the
defect map. Iteration therefore does not necessarily repair idempotence. -/
theorem noncentral_defect_iteration_fixed_point (n : ℕ) :
    ∃ x y : Matrix (Fin 2) (Fin 2) ℤ,
      x * y ≠ y * x ∧ x ≠ 0 ∧ defect^[n] x = x := by
  let x : Matrix (Fin 2) (Fin 2) ℤ := !![2, 2; 0, 0]
  let y : Matrix (Fin 2) (Fin 2) ℤ := !![0, 0; 1, 0]
  refine ⟨x, y, ?_, ?_, ?_⟩
  · decide
  · decide
  · have hx : defect x = x := by decide
    exact Function.iterate_fixed hx n

open DyadicSchurDescent

/-- The noncommuting coefficient witness admits an actual unit-pivot
reduction. Strict reachability and endpoint idempotence are consequences of
the general descent theorems, rather than assumptions on the witness. -/
theorem one_step_noncommuting_idempotent_descent :
    let b : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
    let c : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
    let M : Stage (Matrix (Fin 2) (Fin 2) ℤ) 1 := !![1, b; c, b]
    Step (A := Matrix (Fin 2) (Fin 2) ℤ) ⟨1, M⟩ ⟨0, 0⟩ ∧
      IsIdempotentElem M ∧ b * c ≠ c * b ∧
      (⟨1, M⟩ : Node (Matrix (Fin 2) (Fin 2) ℤ)) < ⟨0, 0⟩ ∧
      IsIdempotentElem (0 : Matrix (Fin 2) (Fin 2) ℤ) := by
  let b : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
  let c : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
  let M : Stage (Matrix (Fin 2) (Fin 2) ℤ) 1 := !![1, b; c, b]
  change Step (A := Matrix (Fin 2) (Fin 2) ℤ) ⟨1, M⟩ ⟨0, 0⟩ ∧
    IsIdempotentElem M ∧ b * c ≠ c * b ∧
    (⟨1, M⟩ : Node (Matrix (Fin 2) (Fin 2) ℤ)) < ⟨0, 0⟩ ∧
    IsIdempotentElem (0 : Matrix (Fin 2) (Fin 2) ℤ)
  have hhead :
      ((1 : (Stage (Matrix (Fin 2) (Fin 2) ℤ) 0)ˣ) :
        Stage (Matrix (Fin 2) (Fin 2) ℤ) 0) = M 0 0 := rfl
  have htail :
      schurTail M (1 : (Stage (Matrix (Fin 2) (Fin 2) ℤ) 0)ˣ) = 0 := by
    change (b - c * (1 : Matrix (Fin 2) (Fin 2) ℤ) * b) = 0
    decide
  have hstep : Step (A := Matrix (Fin 2) (Fin 2) ℤ) ⟨1, M⟩ ⟨0, 0⟩ := by
    have h := Step.reduce (A := Matrix (Fin 2) (Fin 2) ℤ) 0 M
      (1 : (Stage (Matrix (Fin 2) (Fin 2) ℤ) 0)ˣ) hhead
    simpa only [htail] using h
  have hM : IsIdempotentElem M := by
    change (!![(1 : Matrix (Fin 2) (Fin 2) ℤ), b; c, b] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)) *
      !![(1 : Matrix (Fin 2) (Fin 2) ℤ), b; c, b] =
      !![(1 : Matrix (Fin 2) (Fin 2) ℤ), b; c, b]
    decide
  have hnc : b * c ≠ c * b := by decide
  refine ⟨hstep, hM, hnc, step_lt hstep, ?_⟩
  exact terminal_idempotent (Relation.ReflTransGen.single hstep) hM

end InfoGeometry.OperatorAlgebra.SchurDefectExamples
