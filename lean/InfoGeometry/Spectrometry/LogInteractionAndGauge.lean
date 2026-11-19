/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite log interaction, diagonal scaling, and gain ambiguity

Standalone finite results; compiler validation is recorded with this deliverable.

Rows represent spectral lines and columns represent samples. All means below
are arithmetic means of the real log entries, with equal weights. The row and
column types are finite and nonempty for the centering and factorization
theorems. No external project module is imported.

The double-centered interaction is unchanged by arbitrary additive row and
column offsets. For positive intensities this includes positive diagonal
scalings. Zero log interaction characterizes an exact positive rank-one
matrix, but does not establish an exponential spatial profile or identify
detector efficiency, sample activity, or a sample-dependent measurement gain.
The gain reparameterization theorems make the latter ambiguity explicit.
-/

namespace InfoGeometry.Spectrometry.LogInteractionAndGauge

open scoped BigOperators

noncomputable section

def mean {K : Type*} [Fintype K] (f : K → ℝ) : ℝ :=
  (∑ k, f k) / (Fintype.card K : ℝ)

theorem mean_add {K : Type*} [Fintype K] (f g : K → ℝ) :
    mean (fun k => f k + g k) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_sub {K : Type*} [Fintype K] (f g : K → ℝ) :
    mean (fun k => f k - g k) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

theorem mean_const {K : Type*} [Fintype K] [Nonempty K] (a : ℝ) :
    mean (fun _ : K => a) = a := by
  have hcard : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card K ≠ 0)
  simp only [mean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hcard]

variable {I J : Type*} [Fintype I] [Fintype J]

def rowMean (L : I → J → ℝ) : I → ℝ :=
  fun i => mean (L i)

def columnMean (L : I → J → ℝ) : J → ℝ :=
  fun j => mean (fun i => L i j)

def grandMean (L : I → J → ℝ) : ℝ :=
  mean (rowMean L)

def interaction (L : I → J → ℝ) : I → J → ℝ :=
  fun i j => L i j - rowMean L i - columnMean L j + grandMean L

/-- The two iterated finite arithmetic means coincide. -/
theorem mean_swap (L : I → J → ℝ) :
    mean (fun i => mean (L i)) = mean (fun j => mean (fun i => L i j)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm]
  congr 1
  ring

theorem mean_columnMean (L : I → J → ℝ) :
    mean (columnMean L) = grandMean L := by
  exact (mean_swap L).symm

theorem reconstruct_from_interaction (L : I → J → ℝ) (i : I) (j : J) :
    L i j = rowMean L i + (columnMean L j - grandMean L) + interaction L i j := by
  unfold interaction
  ring

variable [Nonempty I] [Nonempty J]

theorem rowMean_add_offsets (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) (i : I) :
    rowMean (fun i j => L i j + a i + b j) i =
      rowMean L i + a i + mean b := by
  simp only [rowMean, mean_add, mean_const]

theorem columnMean_add_offsets (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) (j : J) :
    columnMean (fun i j => L i j + a i + b j) j =
      columnMean L j + mean a + b j := by
  simp only [columnMean, mean_add, mean_const]

theorem grandMean_add_offsets (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) :
    grandMean (fun i j => L i j + a i + b j) =
      grandMean L + mean a + mean b := by
  change mean (fun i => rowMean (fun i j => L i j + a i + b j) i) =
    mean (rowMean L) + mean a + mean b
  simp only [rowMean_add_offsets, mean_add, mean_const]

/-- Actual finite double centering removes arbitrary row and column offsets. -/
theorem interaction_add_offsets (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ)
    (i : I) (j : J) :
    interaction (fun i j => L i j + a i + b j) i j = interaction L i j := by
  simp only [interaction, rowMean_add_offsets, columnMean_add_offsets,
    grandMean_add_offsets]
  ring

theorem rowMean_interaction (L : I → J → ℝ) (i : I) :
    rowMean (interaction L) i = 0 := by
  change mean (fun j => L i j - rowMean L i - columnMean L j + grandMean L) = 0
  simp only [mean_add, mean_sub, mean_const]
  change rowMean L i - rowMean L i - mean (columnMean L) + grandMean L = 0
  rw [mean_columnMean]
  ring

theorem columnMean_interaction (L : I → J → ℝ) (j : J) :
    columnMean (interaction L) j = 0 := by
  change mean (fun i => L i j - rowMean L i - columnMean L j + grandMean L) = 0
  simp only [mean_add, mean_sub, mean_const]
  change columnMean L j - grandMean L - columnMean L j + grandMean L = 0
  ring

theorem interaction_zero (i : I) (j : J) :
    interaction (fun _ : I => fun _ : J => (0 : ℝ)) i j = 0 := by
  simp [interaction, rowMean, columnMean, grandMean, mean]

theorem interaction_additive (a : I → ℝ) (b : J → ℝ) (i : I) (j : J) :
    interaction (fun i j => a i + b j) i j = 0 := by
  simpa only [zero_add, interaction_zero] using
    interaction_add_offsets (fun _ : I => fun _ : J => (0 : ℝ)) a b i j

theorem interaction_zero_iff_additive (L : I → J → ℝ) :
    (∀ i j, interaction L i j = 0) ↔
      ∃ a : I → ℝ, ∃ b : J → ℝ, ∀ i j, L i j = a i + b j := by
  constructor
  · intro hzero
    refine ⟨rowMean L, fun j => columnMean L j - grandMean L, ?_⟩
    intro i j
    have h := hzero i j
    unfold interaction at h
    change L i j = rowMean L i + (columnMean L j - grandMean L)
    linarith
  · rintro ⟨a, b, hab⟩ i j
    have hL : L = fun i j => a i + b j := by
      funext i j
      exact hab i j
    rw [hL]
    exact interaction_additive a b i j

/-- Explicit positive factors obtained from the finite log means. -/
theorem exp_factorization_of_zero_interaction (L : I → J → ℝ)
    (hzero : ∀ i j, interaction L i j = 0) (i : I) (j : J) :
    Real.exp (L i j) =
      Real.exp (rowMean L i) * Real.exp (columnMean L j - grandMean L) := by
  have hlog : L i j = rowMean L i + (columnMean L j - grandMean L) := by
    have h := hzero i j
    unfold interaction at h
    linarith
  rw [hlog, Real.exp_add]

/-- For positive entries, zero interaction of the logs is exactly positive
rank one. No relation between the different sample factors is asserted. -/
theorem log_interaction_zero_iff_positive_rank_one (X : I → J → ℝ)
    (hX : ∀ i j, 0 < X i j) :
    (∀ i j, interaction (fun i j => Real.log (X i j)) i j = 0) ↔
      ∃ p : I → ℝ, ∃ q : J → ℝ,
        (∀ i, 0 < p i) ∧ (∀ j, 0 < q j) ∧ ∀ i j, X i j = p i * q j := by
  constructor
  · intro hzero
    let L : I → J → ℝ := fun i j => Real.log (X i j)
    refine ⟨fun i => Real.exp (rowMean L i),
      fun j => Real.exp (columnMean L j - grandMean L), ?_, ?_, ?_⟩
    · intro i
      exact Real.exp_pos _
    · intro j
      exact Real.exp_pos _
    · intro i j
      calc
        X i j = Real.exp (L i j) := (Real.exp_log (hX i j)).symm
        _ = _ := exp_factorization_of_zero_interaction L hzero i j
  · rintro ⟨p, q, hp, hq, hpq⟩
    apply (interaction_zero_iff_additive (fun i j => Real.log (X i j))).2
    refine ⟨fun i => Real.log (p i), fun j => Real.log (q j), ?_⟩
    intro i j
    rw [hpq i j, Real.log_mul (hp i).ne' (hq j).ne']

/-- Positive diagonal rescaling leaves the double-centered log matrix fixed. -/
theorem log_interaction_diagonal_scaling (X : I → J → ℝ)
    (r : I → ℝ) (c : J → ℝ)
    (hX : ∀ i j, 0 < X i j) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (i : I) (j : J) :
    interaction (fun i j => Real.log (r i * X i j * c j)) i j =
      interaction (fun i j => Real.log (X i j)) i j := by
  have hlogs : (fun i j => Real.log (r i * X i j * c j)) =
      (fun i j => Real.log (X i j) + Real.log (r i) + Real.log (c j)) := by
    funext i j
    rw [Real.log_mul (mul_ne_zero (hr i).ne' (hX i j).ne') (hc j).ne',
      Real.log_mul (hr i).ne' (hX i j).ne']
    ring
  rw [hlogs]
  exact interaction_add_offsets _ _ _ i j

theorem additive_gauge_invariance (a : I → ℝ) (b : J → ℝ) (t : ℝ)
    (i : I) (j : J) :
    (a i + t) + (b j - t) = a i + b j := by
  ring

/-- An additive row-column representation is unique up to one scalar gauge. -/
theorem additive_factors_unique_up_to_gauge
    (a a' : I → ℝ) (b b' : J → ℝ)
    (h : ∀ i j, a i + b j = a' i + b' j) :
    ∃ t : ℝ, (∀ i, a' i = a i + t) ∧ (∀ j, b' j = b j - t) := by
  obtain ⟨j₀⟩ := ‹Nonempty J›
  refine ⟨b j₀ - b' j₀, ?_, ?_⟩
  · intro i
    have hi := h i j₀
    linarith
  · obtain ⟨i₀⟩ := ‹Nonempty I›
    intro j
    have h₀ := h i₀ j₀
    have hj := h i₀ j
    linarith

/-- A nonzero sample-dependent multiplier can be moved between activity and
common column gain while preserving every observed line intensity. -/
theorem activity_gain_reparameterization (response : I → ℝ)
    (activity gain multiplier : J → ℝ) (hm : ∀ j, multiplier j ≠ 0)
    (i : I) (j : J) :
    response i * ((activity j * multiplier j) * (gain j / multiplier j)) =
      response i * (activity j * gain j) := by
  field_simp [hm j]

/-- Even strict positivity leaves activity and gain nonidentifiable: a
different positive activity function has exactly the same product with an
appropriately changed positive gain function. -/
theorem positive_activity_gain_ambiguity (activity gain : J → ℝ)
    (ha : ∀ j, 0 < activity j) (hg : ∀ j, 0 < gain j) :
    ∃ activity' gain' : J → ℝ,
      (∀ j, 0 < activity' j) ∧ (∀ j, 0 < gain' j) ∧
      (∀ j, activity' j * gain' j = activity j * gain j) ∧ activity' ≠ activity := by
  refine ⟨fun j => 2 * activity j, fun j => gain j / 2, ?_, ?_, ?_, ?_⟩
  · intro j
    exact mul_pos (by norm_num) (ha j)
  · intro j
    exact div_pos (hg j) (by norm_num)
  · intro j
    ring
  · intro heq
    obtain ⟨j₀⟩ := ‹Nonempty J›
    have hj := congrFun heq j₀
    have hpositive := ha j₀
    change 2 * activity j₀ = activity j₀ at hj
    linarith

end
end InfoGeometry.Spectrometry.LogInteractionAndGauge
