/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spectrometry.ExactTwoLineRoot
import Mathlib.Tactic

/-!
# Constructing a positive balanced two-line matrix from the scalar root

For a finite nonempty column type, the exact score root produces a strictly
positive matrix with row margins `1/2` and column margins `1/card J`.
The matrix is explicitly a positive diagonal scaling of the kernel whose
two rows are `exp z` and `exp (-z)`. The marginal identities are proved from
the score equation, not assumed. This construction makes no assertion about
convergence of a general Sinkhorn iteration or physical identifiability.

Compiler validation is recorded with this standalone deliverable.
-/

namespace InfoGeometry.Spectrometry.TwoLineBalancedConstruction

open scoped BigOperators
open ExactTwoLineRoot

noncomputable section

variable {J : Type*} [Fintype J] [Nonempty J]

def shifted (z : J → ℝ) (delta : ℝ) (j : J) : ℝ := z j - delta / 2

def denominator (z : J → ℝ) (delta : ℝ) (j : J) : ℝ :=
  2 * (Fintype.card J : ℝ) * Real.cosh (shifted z delta j)

def first (z : J → ℝ) (delta : ℝ) (j : J) : ℝ :=
  Real.exp (shifted z delta j) / denominator z delta j

def second (z : J → ℝ) (delta : ℝ) (j : J) : ℝ :=
  Real.exp (-shifted z delta j) / denominator z delta j

private theorem card_pos_real : 0 < (Fintype.card J : ℝ) := by
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J)

theorem denominator_pos (z : J → ℝ) (delta : ℝ) (j : J) :
    0 < denominator z delta j := by
  exact mul_pos (mul_pos (by norm_num) card_pos_real) (Real.cosh_pos _)

theorem first_pos (z : J → ℝ) (delta : ℝ) (j : J) : 0 < first z delta j :=
  div_pos (Real.exp_pos _) (denominator_pos z delta j)

theorem second_pos (z : J → ℝ) (delta : ℝ) (j : J) : 0 < second z delta j :=
  div_pos (Real.exp_pos _) (denominator_pos z delta j)

theorem first_eq_tanh (z : J → ℝ) (delta : ℝ) (j : J) :
    first z delta j =
      (1 + Real.tanh (shifted z delta j)) / (2 * (Fintype.card J : ℝ)) := by
  unfold first denominator
  rw [← Real.cosh_add_sinh, Real.tanh_eq_sinh_div_cosh]
  field_simp [card_pos_real.ne', (Real.cosh_pos (shifted z delta j)).ne']

theorem second_eq_tanh (z : J → ℝ) (delta : ℝ) (j : J) :
    second z delta j =
      (1 - Real.tanh (shifted z delta j)) / (2 * (Fintype.card J : ℝ)) := by
  unfold second denominator
  rw [← Real.cosh_sub_sinh, Real.tanh_eq_sinh_div_cosh]
  field_simp [card_pos_real.ne', (Real.cosh_pos (shifted z delta j)).ne']

/-- Every column is normalized, for every value of the scalar parameter. -/
theorem column_sum (z : J → ℝ) (delta : ℝ) (j : J) :
    first z delta j + second z delta j = 1 / (Fintype.card J : ℝ) := by
  rw [first_eq_tanh, second_eq_tanh]
  field_simp [card_pos_real.ne']
  ring

/-- The scalar score equation supplies the first row margin. -/
theorem first_row_sum (z : J → ℝ) (delta : ℝ) (hroot : score z delta = 0) :
    (∑ j, first z delta j) = (1 / 2 : ℝ) := by
  simp_rw [first_eq_tanh]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  change ((Fintype.card J : ℝ) + score z delta) /
    (2 * (Fintype.card J : ℝ)) = 1 / 2
  rw [hroot]
  field_simp [card_pos_real.ne']
  ring

/-- The same scalar equation supplies the second row margin. -/
theorem second_row_sum (z : J → ℝ) (delta : ℝ) (hroot : score z delta = 0) :
    (∑ j, second z delta j) = (1 / 2 : ℝ) := by
  simp_rw [second_eq_tanh]
  rw [← Finset.sum_div]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  change ((Fintype.card J : ℝ) - score z delta) /
    (2 * (Fintype.card J : ℝ)) = 1 / 2
  rw [hroot]
  field_simp [card_pos_real.ne']
  ring

def columnFactor (z : J → ℝ) (delta : ℝ) (j : J) : ℝ :=
  1 / denominator z delta j

theorem columnFactor_pos (z : J → ℝ) (delta : ℝ) (j : J) :
    0 < columnFactor z delta j :=
  div_pos (by norm_num) (denominator_pos z delta j)

omit [Nonempty J] in
theorem first_diagonal_scaling (z : J → ℝ) (delta : ℝ) (j : J) :
    first z delta j =
      Real.exp (-delta / 2) * Real.exp (z j) * columnFactor z delta j := by
  have hexp : Real.exp (-delta / 2) * Real.exp (z j) =
      Real.exp (shifted z delta j) := by
    rw [← Real.exp_add]
    congr 1
    unfold shifted
    ring
  unfold first columnFactor
  rw [hexp]
  ring

omit [Nonempty J] in
theorem second_diagonal_scaling (z : J → ℝ) (delta : ℝ) (j : J) :
    second z delta j =
      Real.exp (delta / 2) * Real.exp (-z j) * columnFactor z delta j := by
  have hexp : Real.exp (delta / 2) * Real.exp (-z j) =
      Real.exp (-shifted z delta j) := by
    rw [← Real.exp_add]
    congr 1
    unfold shifted
    ring
  unfold second columnFactor
  rw [hexp]
  ring

def kernel (z : J → ℝ) (i : Fin 2) (j : J) : ℝ :=
  if i = 0 then Real.exp (z j) else Real.exp (-z j)

def rowFactor (delta : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then Real.exp (-delta / 2) else Real.exp (delta / 2)

def plan (z : J → ℝ) (delta : ℝ) (i : Fin 2) (j : J) : ℝ :=
  if i = 0 then first z delta j else second z delta j

theorem rowFactor_pos (delta : ℝ) (i : Fin 2) : 0 < rowFactor delta i := by
  unfold rowFactor
  split <;> exact Real.exp_pos _

theorem plan_pos (z : J → ℝ) (delta : ℝ) (i : Fin 2) (j : J) :
    0 < plan z delta i j := by
  unfold plan
  split
  · exact first_pos z delta j
  · exact second_pos z delta j

omit [Nonempty J] in
theorem plan_diagonal_scaling (z : J → ℝ) (delta : ℝ) (i : Fin 2) (j : J) :
    plan z delta i j = rowFactor delta i * kernel z i j * columnFactor z delta j := by
  by_cases hi : i = 0
  · simpa only [plan, rowFactor, kernel, hi, ite_true] using
      first_diagonal_scaling z delta j
  · simpa only [plan, rowFactor, kernel, hi, ite_false] using
      second_diagonal_scaling z delta j

theorem plan_column_sum (z : J → ℝ) (delta : ℝ) (j : J) :
    (∑ i : Fin 2, plan z delta i j) = 1 / (Fintype.card J : ℝ) := by
  simpa [Fin.sum_univ_two, plan] using column_sum z delta j

theorem plan_row_sum (z : J → ℝ) (delta : ℝ) (hroot : score z delta = 0)
    (i : Fin 2) : (∑ j, plan z delta i j) = (1 / 2 : ℝ) := by
  fin_cases i
  · simpa [plan] using first_row_sum z delta hroot
  · simpa [plan] using second_row_sum z delta hroot

/-- The root theorem constructs positive diagonal factors and both target
margins, for every finite nonempty two-line exponential kernel. No margin
or convergence condition occurs in the hypotheses. -/
theorem exists_positive_balanced_diagonal_scaling (z : J → ℝ) :
    ∃ delta : ℝ,
      score z delta = 0 ∧
      (∀ i : Fin 2, 0 < rowFactor delta i) ∧
      (∀ j, 0 < columnFactor z delta j) ∧
      (∀ i j, 0 < plan z delta i j) ∧
      (∀ i j, plan z delta i j =
        rowFactor delta i * kernel z i j * columnFactor z delta j) ∧
      (∀ i : Fin 2, (∑ j, plan z delta i j) = (1 / 2 : ℝ)) ∧
      (∀ j, (∑ i : Fin 2, plan z delta i j) = 1 / (Fintype.card J : ℝ)) := by
  let M : ℝ := ∑ j, |z j|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ => abs_nonneg (z j))
  have hbound : ∀ j, |z j| ≤ M := by
    intro j
    exact Finset.single_le_sum (fun k _ => abs_nonneg (z k)) (Finset.mem_univ j)
  obtain ⟨delta, _, hroot⟩ := exists_root_bracket z M hM hbound
  exact ⟨delta, hroot, rowFactor_pos delta, columnFactor_pos z delta,
    plan_pos z delta, plan_diagonal_scaling z delta, plan_row_sum z delta hroot,
    plan_column_sum z delta⟩

end
end InfoGeometry.Spectrometry.TwoLineBalancedConstruction
