/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Diagonal scaling, log interactions, and rank-one balancing

The separable observation model uses native `Matrix.vecMulVec`.
All logarithmic bridges state strict positivity hypotheses. Finite log means
use uniform weights on nonempty index types. They are geometric centering,
whereas the balancing targets below are arithmetic row and column sums.

The results establish exact identities, a rank-one balancing construction,
and one log-domain row-normalization step. They do not assert convergence,
optimality, noise reduction, or physical identifiability of a Sinkhorn iteration.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Spectrometry.TableBalancing


variable {I J : Type*}

def diagonalScale (r : I → ℝ) (c : J → ℝ) (M : I → J → ℝ) : I → J → ℝ :=
  fun i j => r i * M i j * c j

def oddsRatio (M : I → J → ℝ) (i k : I) (j l : J) : ℝ :=
  (M i j * M k l) / (M i l * M k j)

theorem diagonalScale_cross_product (r : I → ℝ) (c : J → ℝ)
    (M : I → J → ℝ) (i k : I) (j l : J) :
    diagonalScale r c M i j * diagonalScale r c M k l =
      (r i * r k * c j * c l) * (M i j * M k l) := by
  unfold diagonalScale
  ring

theorem diagonalScale_minor (r : I → ℝ) (c : J → ℝ)
    (M : I → J → ℝ) (i k : I) (j l : J) :
    diagonalScale r c M i j * diagonalScale r c M k l -
      diagonalScale r c M i l * diagonalScale r c M k j =
    (r i * r k * c j * c l) * (M i j * M k l - M i l * M k j) := by
  unfold diagonalScale
  ring

theorem diagonalScale_oddsRatio (r : I → ℝ) (c : J → ℝ)
    (M : I → J → ℝ) (i k : I) (j l : J)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0)
    (hM : ∀ i j, M i j ≠ 0) :
    oddsRatio (diagonalScale r c M) i k j l = oddsRatio M i k j l := by
  unfold oddsRatio diagonalScale
  field_simp [hr i, hr k, hc j, hc l, hM i l, hM k j]

theorem diagonalScale_pos (r : I → ℝ) (c : J → ℝ) (M : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : ∀ i j, 0 < M i j)
    (i : I) (j : J) : 0 < diagonalScale r c M i j :=
  mul_pos (mul_pos (hr i) (hM i j)) (hc j)

/-- A reciprocal scalar change in the scaling factors does not change the matrix. -/
theorem diagonalScale_gauge (r : I → ℝ) (c : J → ℝ) (M : I → J → ℝ)
    (t : ℝ) (ht : t ≠ 0) :
    diagonalScale (fun i => t * r i) (fun j => c j / t) M =
      diagonalScale r c M := by
  funext i j
  unfold diagonalScale
  field_simp [ht]

def entryLog (M : I → J → ℝ) : I → J → ℝ := fun i j => Real.log (M i j)

def addGauge (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) : I → J → ℝ :=
  fun i j => L i j + a i + b j

theorem entryLog_diagonalScale (r : I → ℝ) (c : J → ℝ) (M : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : ∀ i j, 0 < M i j) :
    entryLog (diagonalScale r c M) =
      addGauge (entryLog M) (fun i => Real.log (r i)) (fun j => Real.log (c j)) := by
  funext i j
  unfold entryLog diagonalScale addGauge
  rw [Real.log_mul (mul_ne_zero (ne_of_gt (hr i)) (ne_of_gt (hM i j)))
    (ne_of_gt (hc j)), Real.log_mul (ne_of_gt (hr i)) (ne_of_gt (hM i j))]
  ring

section FiniteMeans

variable [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- Uniform finite arithmetic mean; the centering theorems assume nonempty indices. -/
def mean (v : I → ℝ) : ℝ := (∑ i, v i) / (Fintype.card I : ℝ)

theorem mean_const (a : ℝ) : mean (fun _ : I => a) = a := by
  have hn : (Fintype.card I : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [mean, hn]

omit [Nonempty I] in
theorem mean_add (a b : I → ℝ) : mean (fun i => a i + b i) = mean a + mean b := by
  simp [mean, Finset.sum_add_distrib, add_div]

omit [Nonempty I] in
theorem mean_sub (a b : I → ℝ) : mean (fun i => a i - b i) = mean a - mean b := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

omit [Nonempty I] in
theorem mean_const_mul (a : ℝ) (v : I → ℝ) :
    mean (fun i => a * v i) = a * mean v := by
  unfold mean
  rw [← Finset.mul_sum]
  ring

omit [Nonempty I] in
theorem mean_mul_const (v : I → ℝ) (a : ℝ) :
    mean (fun i => v i * a) = mean v * a := by
  unfold mean
  rw [← Finset.sum_mul]
  ring

omit [Nonempty I] in
theorem mean_neg (v : I → ℝ) : mean (fun i => -v i) = -mean v := by
  simp [mean, Finset.sum_neg_distrib, neg_div]

omit [Nonempty I] [Nonempty J] in
theorem mean_mean_comm (L : I → J → ℝ) :
    mean (fun i => mean (L i)) = mean (fun j => mean (fun i => L i j)) := by
  unfold mean
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

def rowMean (L : I → J → ℝ) (i : I) : ℝ := mean (L i)
def colMean (L : I → J → ℝ) (j : J) : ℝ := mean (fun i => L i j)
def grandMean (L : I → J → ℝ) : ℝ := mean (rowMean L)

omit [Nonempty I] [Nonempty J] in
theorem mean_colMean (L : I → J → ℝ) : mean (colMean L) = grandMean L :=
  (mean_mean_comm L).symm

def rowEffect (L : I → J → ℝ) (i : I) : ℝ := rowMean L i - grandMean L
def colEffect (L : I → J → ℝ) (j : J) : ℝ := colMean L j - grandMean L

def doubleCenter (L : I → J → ℝ) (i : I) (j : J) : ℝ :=
  L i j - rowMean L i - colMean L j + grandMean L

omit [Nonempty J] in
theorem mean_rowEffect (L : I → J → ℝ) : mean (rowEffect L) = 0 := by
  unfold rowEffect
  rw [mean_sub, mean_const]
  exact sub_self _

omit [Nonempty I] in
theorem mean_colEffect (L : I → J → ℝ) : mean (colEffect L) = 0 := by
  unfold colEffect
  rw [mean_sub, mean_const, mean_colMean]
  exact sub_self _

omit [Nonempty I] [Nonempty J] in
/-- The grand intercept is essential when both effects are constrained to mean zero. -/
theorem log_decomposition (L : I → J → ℝ) (i : I) (j : J) :
    L i j = grandMean L + rowEffect L i + colEffect L j + doubleCenter L i j := by
  unfold rowEffect colEffect doubleCenter
  ring

omit [Nonempty I] in
theorem rowMean_doubleCenter (L : I → J → ℝ) (i : I) :
    rowMean (doubleCenter L) i = 0 := by
  unfold rowMean doubleCenter
  rw [mean_add, mean_sub, mean_sub, mean_const, mean_const, mean_colMean]
  unfold rowMean
  ring

omit [Nonempty J] in
theorem colMean_doubleCenter (L : I → J → ℝ) (j : J) :
    colMean (doubleCenter L) j = 0 := by
  unfold colMean doubleCenter
  rw [mean_add, mean_sub, mean_sub, mean_const, mean_const]
  change mean (fun i => L i j) - grandMean L - mean (fun i => L i j) + grandMean L = 0
  ring

omit [Fintype I] [Nonempty I] in
theorem rowMean_addGauge (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) (i : I) :
    rowMean (addGauge L a b) i = rowMean L i + a i + mean b := by
  change mean (fun j => L i j + a i + b j) = mean (L i) + a i + mean b
  rw [mean_add, mean_add, mean_const]

omit [Fintype J] [Nonempty J] in
theorem colMean_addGauge (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) (j : J) :
    colMean (addGauge L a b) j = colMean L j + mean a + b j := by
  simp [colMean, addGauge, mean_add, mean_const]

theorem grandMean_addGauge (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) :
    grandMean (addGauge L a b) = grandMean L + mean a + mean b := by
  change mean (fun i => rowMean (addGauge L a b) i) =
    mean (rowMean L) + mean a + mean b
  simp only [rowMean_addGauge, mean_add, mean_const]

theorem doubleCenter_addGauge (L : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) :
    doubleCenter (addGauge L a b) = doubleCenter L := by
  funext i j
  simp only [doubleCenter, addGauge, rowMean_addGauge, colMean_addGauge,
    grandMean_addGauge]
  ring

omit [Nonempty I] [Nonempty J] in
@[simp] theorem doubleCenter_zero : doubleCenter (0 : I → J → ℝ) = 0 := by
  funext i j
  simp [doubleCenter, rowMean, colMean, grandMean, mean]

theorem doubleCenter_additive (a : I → ℝ) (b : J → ℝ) :
    doubleCenter (fun i j => a i + b j) = 0 := by
  have hfun : addGauge (0 : I → J → ℝ) a b = fun i j => a i + b j := by
    funext i j
    simp [addGauge]
  rw [← hfun, doubleCenter_addGauge, doubleCenter_zero]

omit [Nonempty I] [Nonempty J] in
theorem doubleCenter_product (a : I → ℝ) (b : J → ℝ) (i : I) (j : J) :
    doubleCenter (Matrix.vecMulVec a b) i j = (a i - mean a) * (b j - mean b) := by
  change doubleCenter (fun i j => a i * b j) i j =
    (a i - mean a) * (b j - mean b)
  have hr : rowMean (fun i j => a i * b j) = fun i => a i * mean b := by
    funext i
    exact mean_const_mul (a i) b
  have hc : colMean (fun i j => a i * b j) = fun j => mean a * b j := by
    funext j
    exact mean_mul_const a (b j)
  have hg : grandMean (fun i j => a i * b j) = mean a * mean b := by
    unfold grandMean
    rw [hr]
    exact mean_mul_const a (mean b)
  simp only [doubleCenter, hr, hc, hg]
  ring

/-- A separable load-by-energy attenuation term survives log centering as an
interaction of centered load and centered attenuation coefficient. -/
theorem attenuation_log_interaction (alpha ell : I → ℝ) (beta kappa : J → ℝ)
    (i : I) (j : J) :
    doubleCenter (fun i j => alpha i + beta j - ell i * kappa j) i j =
      -(ell i - mean ell) * (kappa j - mean kappa) := by
  have hfun : (fun i j => alpha i + beta j - ell i * kappa j) =
      addGauge (fun i j => -ell i * kappa j) alpha beta := by
    funext i j
    unfold addGauge
    ring
  have hproduct := doubleCenter_product (fun k => -ell k) kappa i j
  change doubleCenter (fun i j => -ell i * kappa j) i j =
    (-ell i - mean (fun k => -ell k)) * (kappa j - mean kappa) at hproduct
  rw [hfun, doubleCenter_addGauge, hproduct, mean_neg]
  ring

theorem doubleCenter_zero_iff_additive (L : I → J → ℝ) :
    (∀ i j, doubleCenter L i j = 0) ↔
      ∃ a : I → ℝ, ∃ b : J → ℝ, ∀ i j, L i j = a i + b j := by
  constructor
  · intro h
    refine ⟨rowMean L, fun j => colMean L j - grandMean L, ?_⟩
    intro i j
    have hij := h i j
    unfold doubleCenter at hij
    linarith
  · rintro ⟨a, b, h⟩ i j
    have hfun : L = fun i j => a i + b j := funext fun i => funext (h i)
    rw [hfun, doubleCenter_additive]
    rfl

/-- Multiplicative row/column scaling preserves the complete centered log interaction. -/
theorem logInteraction_diagonalScale (r : I → ℝ) (c : J → ℝ) (M : I → J → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (hM : ∀ i j, 0 < M i j) :
    doubleCenter (entryLog (diagonalScale r c M)) = doubleCenter (entryLog M) := by
  rw [entryLog_diagonalScale r c M hr hc hM, doubleCenter_addGauge]

theorem logInteraction_rateMatrix (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) :
    doubleCenter (entryLog (Matrix.vecMulVec a b)) = 0 := by
  have hlog : entryLog (Matrix.vecMulVec a b) = fun i j => Real.log (a i) + Real.log (b j) := by
    funext i j
    exact Real.log_mul (ne_of_gt (ha i)) (ne_of_gt (hb j))
  rw [hlog, doubleCenter_additive]

/-- Zero log interaction is equivalent to a positive rank-one factorization. -/
theorem logInteraction_zero_iff_rank_one (M : I → J → ℝ)
    (hM : ∀ i j, 0 < M i j) :
    (∀ i j, doubleCenter (entryLog M) i j = 0) ↔
      ∃ a : I → ℝ, ∃ b : J → ℝ,
        (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧ M = Matrix.vecMulVec a b := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := (doubleCenter_zero_iff_additive (entryLog M)).mp h
    refine ⟨fun i => Real.exp (a i), fun j => Real.exp (b j),
      fun i => Real.exp_pos _, fun j => Real.exp_pos _, ?_⟩
    funext i j
    calc
      M i j = Real.exp (entryLog M i j) := (Real.exp_log (hM i j)).symm
      _ = Real.exp (a i + b j) := congrArg Real.exp (hab i j)
      _ = Matrix.vecMulVec (fun i => Real.exp (a i)) (fun j => Real.exp (b j)) i j :=
        Real.exp_add _ _
  · rintro ⟨a, b, ha, hb, h⟩ i j
    rw [h, logInteraction_rateMatrix a b ha hb]
    rfl

/-- Exponential of the arithmetic log mean: the geometric mean for positive data. -/
def geometricMean (v : I → ℝ) : ℝ := Real.exp (mean (fun i => Real.log (v i)))

omit [Nonempty I] in
theorem geometricMean_pos (v : I → ℝ) : 0 < geometricMean v := Real.exp_pos _

def centeredLog (v : I → ℝ) (i : I) : ℝ := Real.log (v i) - mean (fun k => Real.log (v k))

theorem mean_centeredLog (v : I → ℝ) : mean (centeredLog v) = 0 := by
  unfold centeredLog
  rw [mean_sub, mean_const]
  exact sub_self _

omit [Nonempty I] in
theorem centeredLog_eq_log_div_geometricMean (v : I → ℝ)
    (hv : ∀ i, 0 < v i) (i : I) :
    centeredLog v i = Real.log (v i / geometricMean v) := by
  rw [Real.log_div (ne_of_gt (hv i)) (ne_of_gt (geometricMean_pos v))]
  simp [centeredLog, geometricMean]

theorem mean_log_scale (v : I → ℝ) (t : ℝ)
    (hv : ∀ i, 0 < v i) (ht : 0 < t) :
    mean (fun i => Real.log (t * v i)) =
      Real.log t + mean (fun i => Real.log (v i)) := by
  have hlog : (fun i => Real.log (t * v i)) =
      fun i => Real.log t + Real.log (v i) := by
    funext i
    exact Real.log_mul (ne_of_gt ht) (ne_of_gt (hv i))
  rw [hlog, mean_add, mean_const]

theorem geometricMean_scale (v : I → ℝ) (t : ℝ)
    (hv : ∀ i, 0 < v i) (ht : 0 < t) :
    geometricMean (fun i => t * v i) = t * geometricMean v := by
  unfold geometricMean
  rw [mean_log_scale v t hv ht, Real.exp_add, Real.exp_log ht]

theorem centeredLog_scale (v : I → ℝ) (t : ℝ)
    (hv : ∀ i, 0 < v i) (ht : 0 < t) :
    centeredLog (fun i => t * v i) = centeredLog v := by
  funext i
  unfold centeredLog
  rw [mean_log_scale v t hv ht, Real.log_mul (ne_of_gt ht) (ne_of_gt (hv i))]
  ring

/-- Rescaling the row factors to geometric mean one supplies a concrete gauge choice. -/
theorem mean_log_normalized_gauge (r : I → ℝ) (hr : ∀ i, 0 < r i) :
    mean (fun i => Real.log (Real.exp (-mean (fun k => Real.log (r k))) * r i)) = 0 := by
  rw [mean_log_scale r _ hr (Real.exp_pos _), Real.log_exp]
  ring

/-- A single mean-log constraint fixes the reciprocal positive scalar gauge. -/
theorem positive_gauge_fixed_by_log_mean (r : I → ℝ) (t : ℝ)
    (hr : ∀ i, 0 < r i) (ht : 0 < t)
    (hmean : mean (fun i => Real.log (t * r i)) = mean (fun i => Real.log (r i))) :
    t = 1 := by
  rw [mean_log_scale r t hr ht] at hmean
  have hz : Real.log t = 0 := by linarith
  calc
    t = Real.exp (Real.log t) := (Real.exp_log ht).symm
    _ = 1 := by rw [hz, Real.exp_zero]

end FiniteMeans

section ArithmeticMarginals

variable [Fintype I] [Fintype J]

def rowSum (M : I → J → ℝ) (i : I) : ℝ := ∑ j, M i j
def colSum (M : I → J → ℝ) (j : J) : ℝ := ∑ i, M i j

omit [Fintype I] in
theorem rowSum_rateMatrix (a : I → ℝ) (b : J → ℝ) (i : I) :
    rowSum (Matrix.vecMulVec a b) i = a i * ∑ j, b j := by
  simp [rowSum, Matrix.vecMulVec, Finset.mul_sum]

omit [Fintype J] in
theorem colSum_rateMatrix (a : I → ℝ) (b : J → ℝ) (j : J) :
    colSum (Matrix.vecMulVec a b) j = (∑ i, a i) * b j := by
  simp [colSum, Matrix.vecMulVec, Finset.sum_mul]

/-- Exact uniqueness of an already balanced rank-one matrix. The second target
total is forced by these marginals; positivity is unnecessary for this algebra. -/
theorem balanced_rank_one_unique (a : I → ℝ) (b : J → ℝ)
    (p : I → ℝ) (q : J → ℝ)
    (hrow : ∀ i, rowSum (Matrix.vecMulVec a b) i = p i)
    (hcol : ∀ j, colSum (Matrix.vecMulVec a b) j = q j)
    (hp : ∑ i, p i = 1) : Matrix.vecMulVec a b = Matrix.vecMulVec p q := by
  have htotal : (∑ i, a i) * (∑ j, b j) = 1 := by
    calc
      (∑ i, a i) * (∑ j, b j) = ∑ i, rowSum (Matrix.vecMulVec a b) i := by
        simp only [rowSum_rateMatrix, Finset.sum_mul]
      _ = ∑ i, p i := Finset.sum_congr rfl (fun i _ => hrow i)
      _ = 1 := hp
  funext i j
  change a i * b j = p i * q j
  rw [← hrow i, ← hcol j, rowSum_rateMatrix, colSum_rateMatrix]
  calc
    a i * b j = a i * b j * 1 := (mul_one _).symm
    _ = a i * b j * ((∑ k, a k) * (∑ l, b l)) := by rw [htotal]
    _ = (a i * ∑ l, b l) * ((∑ k, a k) * b j) := by ring

omit [Fintype I] [Fintype J] in
theorem diagonalScale_rateMatrix (r a : I → ℝ) (c b : J → ℝ) :
    diagonalScale r c (Matrix.vecMulVec a b) =
      Matrix.vecMulVec (fun i => r i * a i) (fun j => c j * b j) := by
  funext i j
  change r i * (a i * b j) * c j = (r i * a i) * (c j * b j)
  ring

theorem balanced_diagonalScale_rank_one (r a : I → ℝ) (c b : J → ℝ)
    (p : I → ℝ) (q : J → ℝ)
    (hrow : ∀ i, rowSum (diagonalScale r c (Matrix.vecMulVec a b)) i = p i)
    (hcol : ∀ j, colSum (diagonalScale r c (Matrix.vecMulVec a b)) j = q j)
    (hp : ∑ i, p i = 1) :
    diagonalScale r c (Matrix.vecMulVec a b) = Matrix.vecMulVec p q := by
  rw [diagonalScale_rateMatrix] at hrow hcol ⊢
  exact balanced_rank_one_unique _ _ p q hrow hcol hp

omit [Fintype I] [Fintype J] in
/-- Algebraic rank-one scaling formula; t is the unresolved positive scalar gauge.
Positivity and normalization of the targets are added in the existence theorem. -/
theorem rank_one_scaling_formula (a : I → ℝ) (b : J → ℝ)
    (p : I → ℝ) (q : J → ℝ) (t : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (ht : 0 < t) :
    diagonalScale (fun i => t * p i / a i) (fun j => q j / (t * b j))
      (Matrix.vecMulVec a b) = Matrix.vecMulVec p q := by
  funext i j
  change (t * p i / a i) * (a i * b j) * (q j / (t * b j)) = p i * q j
  field_simp [ne_of_gt (ha i), ne_of_gt (hb j), ne_of_gt ht] <;> ring

theorem positive_rank_one_balancing_exists (a : I → ℝ) (b : J → ℝ)
    (p : I → ℝ) (q : J → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hp : ∀ i, 0 < p i) (hq : ∀ j, 0 < q j)
    (hpSum : ∑ i, p i = 1) (hqSum : ∑ j, q j = 1) :
    ∃ r : I → ℝ, ∃ c : J → ℝ,
      (∀ i, 0 < r i) ∧ (∀ j, 0 < c j) ∧
      (∀ i, rowSum (diagonalScale r c (Matrix.vecMulVec a b)) i = p i) ∧
      (∀ j, colSum (diagonalScale r c (Matrix.vecMulVec a b)) j = q j) := by
  refine ⟨fun i => 1 * p i / a i, fun j => q j / (1 * b j), ?_, ?_, ?_, ?_⟩
  · intro i
    exact div_pos (mul_pos zero_lt_one (hp i)) (ha i)
  · intro j
    exact div_pos (hq j) (mul_pos zero_lt_one (hb j))
  · intro i
    rw [rank_one_scaling_formula a b p q 1 ha hb zero_lt_one, rowSum_rateMatrix, hqSum,
      mul_one]
  · intro j
    rw [rank_one_scaling_formula a b p q 1 ha hb zero_lt_one, colSum_rateMatrix, hpSum,
      one_mul]

/-- Unit total on a 9-by-5 rank-one table gives entries 1/45 under uniform targets. -/
theorem balanced_nine_by_five (a : Fin 9 → ℝ) (b : Fin 5 → ℝ)
    (hrow : ∀ i, rowSum (Matrix.vecMulVec a b) i = 1 / 9)
    (hcol : ∀ j, colSum (Matrix.vecMulVec a b) j = 1 / 5) (i : Fin 9) (j : Fin 5) :
    Matrix.vecMulVec a b i j = 1 / 45 := by
  have h := balanced_rank_one_unique a b (fun _ => 1 / 9) (fun _ => 1 / 5)
    hrow hcol (by norm_num)
  rw [h]
  norm_num [Matrix.vecMulVec]

end ArithmeticMarginals

section LogSumExp

variable [Fintype J] [Nonempty J]

def logSumExp (z : J → ℝ) : ℝ := Real.log (∑ j, Real.exp (z j))

theorem sum_exp_pos (z : J → ℝ) : 0 < ∑ j, Real.exp (z j) := by
  classical
  exact Finset.sum_pos (fun j _ => Real.exp_pos (z j)) Finset.univ_nonempty

/-- The exact shift identity underlying a stable log-sum-exp evaluation. -/
theorem logSumExp_shift (z : J → ℝ) (a : ℝ) :
    logSumExp (fun j => a + z j) = a + logSumExp z := by
  unfold logSumExp
  simp only [Real.exp_add, ← Finset.mul_sum]
  rw [Real.log_mul (ne_of_gt (Real.exp_pos a)) (ne_of_gt (sum_exp_pos z)), Real.log_exp]

theorem logSumExp_stable_shift (z : J → ℝ) (m : ℝ) :
    logSumExp z = m + Real.log (∑ j, Real.exp (z j - m)) := by
  have h := logSumExp_shift (fun j => z j - m) m
  have hshift : (fun j => m + (z j - m)) = z := by
    funext j
    ring
  rw [hshift] at h
  exact h

/-- One log-domain row update enforces the prescribed arithmetic row total.
This is a single exact step, with no claim about alternating-step convergence. -/
theorem log_row_normalization (z : J → ℝ) (p : ℝ) (hp : 0 < p) :
    (∑ j, Real.exp (Real.log p - logSumExp z + z j)) = p := by
  simp only [Real.exp_add, Real.exp_sub, ← Finset.mul_sum]
  rw [Real.exp_log hp]
  unfold logSumExp
  rw [Real.exp_log (sum_exp_pos z)]
  exact div_mul_cancel₀ p (ne_of_gt (sum_exp_pos z))

end LogSumExp

end InfoGeometry.Spectrometry.TableBalancing
