/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Quantum.ChoiCompletePositivity
import Mathlib.Data.Matrix.Basis

/-!
# A fixed effect that does not commute with its Kraus operators

The four operators below satisfy the trace-preserving completeness relation.
Their backward action is the existing `Choi.krausMap` at the adjointed family,
so its multiplication order is exactly `∑ a, K a † * X * K a`.

The positive effect and its positive complement are explicit diagonal matrices
on the full three-dimensional complex carrier. The effect is fixed, but it
does not commute with the transfer operators. Its square is not fixed, and
the opposite Kraus completeness relation fails. Thus fixedness alone does
not identify the effect with the common commutant or force multiplicative
closure of the fixed operators.
-/

noncomputable section

namespace InfoGeometry.Quantum.KrausFixedEffectCounterexample

open scoped BigOperators ComplexOrder

local notation "Mat" => Matrix (Fin 3) (Fin 3) ℂ

/-- `E₀₀`, `E₁₁`, `(3/5) E₀₂`, and `(4/5) E₁₂`, using native matrix units. -/
def K : Fin 4 → Mat :=
  ![Matrix.single 0 0 1, Matrix.single 1 1 1,
    Matrix.single 0 2 (3 / 5), Matrix.single 1 2 (4 / 5)]

/-- A nonconstant effect with eigenvalues zero, one, and sixteen twenty-fifths. -/
def effect : Mat := Matrix.diagonal ![0, 1, 16 / 25]

/-- The family is complete in the trace-preserving direction. -/
theorem kraus_complete : (∑ a : Fin 4, star (K a) * K a) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, Matrix.mul_apply, Matrix.star_apply, Matrix.single,
      Complex.conj_ofNat, Fin.sum_univ_succ]

theorem effect_posSemidef : effect.PosSemidef := by
  unfold effect
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem effect_complement_posSemidef : (1 - effect).PosSemidef := by
  have hcomplement : (1 : Mat) - effect = Matrix.diagonal ![1, 0, (9 / 25 : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [effect, Matrix.diagonal, Matrix.one_apply]
  rw [hcomplement]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

/-- The exact backward Kraus action fixes this effect. -/
theorem effect_fixed :
    Choi.krausMap (fun a => star (K a)) effect = effect := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Choi.krausMap, K, effect, Matrix.mul_apply, Matrix.star_apply,
      Matrix.single, Matrix.diagonal, Complex.conj_ofNat, Fin.sum_univ_succ]

/-- The effect's commutator with the first transfer operator is nonzero. -/
theorem effect_commutator_two :
    effect * K 2 - K 2 * effect =
      (-48 / 125 : ℂ) • Matrix.single 0 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, effect, Matrix.mul_apply, Matrix.single, Matrix.diagonal,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ]

/-- The second transfer operator has a different nonzero commutator. -/
theorem effect_commutator_three :
    effect * K 3 - K 3 * effect =
      (36 / 125 : ℂ) • Matrix.single 1 2 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, effect, Matrix.mul_apply, Matrix.single, Matrix.diagonal,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ]

/-- This is inequality of actual ordered matrix products. -/
theorem effect_mul_kraus_ne : effect * K 2 ≠ K 2 * effect := by
  intro h
  have hzero : (effect * K 2 - K 2 * effect) 0 2 = 0 := by
    simp [h]
  rw [effect_commutator_two] at hzero
  norm_num [Matrix.single, Matrix.smul_apply, smul_eq_mul] at hzero

/-- A complete Kraus family can fix a positive effect outside its common commutant. -/
theorem exists_fixed_effect_outside_kraus_commutant :
    ∃ E A : Matrix (Fin 3) (Fin 3) ℂ,
      E * A ≠ A * E ∧
      E.PosSemidef ∧ (1 - E).PosSemidef ∧
      Choi.krausMap (fun a => star (K a)) E = E ∧
      A = K 2 ∧ (∑ a : Fin 4, star (K a) * K a) = 1 := by
  exact ⟨effect, K 2, effect_mul_kraus_ne, effect_posSemidef,
    effect_complement_posSemidef, effect_fixed, rfl, kraus_complete⟩

/-- The opposite completeness relation fails, so the forward map is not unital. -/
theorem reverse_completeness_fails :
    (∑ a : Fin 4, K a * star (K a)) ≠ (1 : Mat) := by
  intro h
  have hentry := congrArg (fun A : Mat => A 2 2) h
  norm_num [K, Matrix.mul_apply, Matrix.star_apply, Matrix.single,
    Matrix.one_apply, Fin.sum_univ_succ] at hentry

/-- Fixed effects need not be closed under squaring for a merely unital backward map. -/
theorem effect_square_not_fixed :
    Choi.krausMap (fun a => star (K a)) (effect * effect) ≠ effect * effect := by
  intro h
  have hentry := congrArg (fun A : Mat => A 2 2) h
  norm_num [Choi.krausMap, K, effect, Matrix.mul_apply, Matrix.star_apply,
    Matrix.single, Matrix.diagonal, Complex.conj_ofNat, Fin.sum_univ_succ] at hentry

end InfoGeometry.Quantum.KrausFixedEffectCounterexample
