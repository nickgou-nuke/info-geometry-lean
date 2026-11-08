/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Matrix.Basic

/-!
# One-sided idempotent absorption does not imply a two-sided partial-flag relation

This finite matrix witness records the exact hypothesis boundary behind the
two-sided nesting equations used by `partial_flag_to_grassmannian_embedding`.
It does not model self-adjoint projections: that additional geometric condition
can force the reverse product equation by taking adjoints.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open Matrix

private def flagWitnessP₁ : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

private def flagWitnessP₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i _j => if i = 0 then 1 else 0

private def letterWitnessZ : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

private def letterWitnessB : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

private def letterWitnessS : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = j then 1 else 0

/-- The two directed matrix units witness noncommutativity in the same carrier
used by the partial-flag counterexample: their products are the two distinct
diagonal matrix units. -/
theorem flagWitness_letter_units_noncommute :
    letterWitnessZ * letterWitnessB ≠ letterWitnessB * letterWitnessZ := by
  decide

/-- The range/right-ideal inclusion encoded by `P₂ * P₁ = P₁` does not by itself
give `P₁ * P₂ = P₁` for arbitrary, possibly non-self-adjoint idempotents. -/
theorem one_sided_idempotent_inclusion_not_two_sided :
    flagWitnessP₁ * flagWitnessP₁ = flagWitnessP₁ ∧
    flagWitnessP₂ * flagWitnessP₂ = flagWitnessP₂ ∧
    flagWitnessP₂ * flagWitnessP₁ = flagWitnessP₁ ∧
    (∀ X : Matrix (Fin 2) (Fin 2) ℤ,
      ∃ Y : Matrix (Fin 2) (Fin 2) ℤ, flagWitnessP₁ * X = flagWitnessP₂ * Y) ∧
    flagWitnessP₁ * flagWitnessP₂ ≠ flagWitnessP₁ := by
  have h₁ : flagWitnessP₁ * flagWitnessP₁ = flagWitnessP₁ := by
    decide
  have h₂ : flagWitnessP₂ * flagWitnessP₂ = flagWitnessP₂ := by
    decide
  have h₂₁ : flagWitnessP₂ * flagWitnessP₁ = flagWitnessP₁ := by
    decide
  refine ⟨h₁, h₂, h₂₁, ?_, ?_⟩
  · intro X
    refine ⟨flagWitnessP₁ * X, ?_⟩
    calc
      flagWitnessP₁ * X = (flagWitnessP₂ * flagWitnessP₁) * X := by rw [h₂₁]
      _ = flagWitnessP₂ * (flagWitnessP₁ * X) := by simp only [mul_assoc]
  · decide

/-- Commuting both factors with the square-root factor does not suffice for
noncommutative rationalization; the two coefficients must also commute with
each other. -/
theorem symbol_rationalization_requires_mutual_coefficient_commutation :
    letterWitnessZ * letterWitnessS = letterWitnessS * letterWitnessZ ∧
    letterWitnessB * letterWitnessS = letterWitnessS * letterWitnessB ∧
    (letterWitnessZ + letterWitnessB * letterWitnessS) *
        (letterWitnessZ - letterWitnessB * letterWitnessS) ≠
      letterWitnessZ * letterWitnessZ -
        letterWitnessB * letterWitnessB * (letterWitnessS * letterWitnessS) := by
  refine ⟨by decide, by decide, ?_⟩
  decide

end InfoGeometry.OperatorAlgebra.PeirceSpine
