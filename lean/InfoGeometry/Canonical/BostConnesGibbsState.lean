import Mathlib.Probability.ProbabilityMassFunction.Basic
import InfoGeometry.Canonical.BostConnesKMS

/-!
# Bost--Connes Gibbs PMF

This file upgrades the normalized Bost--Connes positive-integer weights from
`BostConnesKMS` into an actual probability mass function on `ℕ+` in the
convergent domain `1 < β`.

It is deliberately only a diagonal Gibbs distribution.  It does not assert a
full C*-algebraic KMS state on the completed Bost--Connes algebra.
-/

open scoped BigOperators

noncomputable section

namespace BostConnesGibbsState

open BostConnesKMS

/--
The normalized Bost--Connes Gibbs probability mass function on positive
integers for inverse temperature `β` in the convergence domain `1 < β`.
-/
def bostConnesPMF (β : ℝ) (hβ : 1 < β) : PMF ℕ+ :=
  ⟨fun n => ENNReal.ofReal (normalizedBostConnesWeight β n),
    ENNReal.summable.hasSum_iff.2 <| by
      have hnonneg : ∀ n : ℕ+, 0 ≤ normalizedBostConnesWeight β n := fun n =>
        le_of_lt (normalizedBostConnesWeight_pos β hβ n)
      have hsummable : Summable (fun n : ℕ+ => normalizedBostConnesWeight β n) := by
        simpa [normalizedBostConnesWeight] using
          (summable_bostConnesWeight β hβ).div_const (bostConnesPartition β)
      rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable]
      rw [tsum_normalizedBostConnesWeight β hβ]
      norm_num⟩

/-- Pointwise readback of the concrete Bost--Connes Gibbs PMF. -/
@[simp] theorem bostConnesPMF_apply
    (β : ℝ) (hβ : 1 < β) (n : ℕ+) :
    bostConnesPMF β hβ n =
      ENNReal.ofReal (normalizedBostConnesWeight β n) :=
  rfl

/-- Diagonal Gibbs expectation of a real arithmetic observable. -/
def bostConnesExpectation
    (β : ℝ) (_hβ : 1 < β) (f : ℕ+ → ℝ) : ℝ :=
  ∑' n : ℕ+, normalizedBostConnesWeight β n * f n

/-- The Gibbs expectation of the constant-one observable is one. -/
theorem bostConnesExpectation_one (β : ℝ) (hβ : 1 < β) :
    bostConnesExpectation β hβ (fun _ : ℕ+ => (1 : ℝ)) = 1 := by
  simp [bostConnesExpectation, tsum_normalizedBostConnesWeight β hβ]

/-- Nonnegative observables have nonnegative Gibbs expectation. -/
theorem bostConnesExpectation_nonneg (β : ℝ) (hβ : 1 < β)
    {f : ℕ+ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    0 ≤ bostConnesExpectation β hβ f := by
  exact tsum_nonneg fun n => mul_nonneg
    (le_of_lt (normalizedBostConnesWeight_pos β hβ n)) (hf n)

/-- Additivity of Gibbs expectation under the corresponding summability hypotheses. -/
theorem bostConnesExpectation_add (β : ℝ) (hβ : 1 < β)
    {f g : ℕ+ → ℝ}
    (hf : Summable fun n : ℕ+ => normalizedBostConnesWeight β n * f n)
    (hg : Summable fun n : ℕ+ => normalizedBostConnesWeight β n * g n) :
    bostConnesExpectation β hβ (fun n => f n + g n) =
      bostConnesExpectation β hβ f + bostConnesExpectation β hβ g := by
  rw [bostConnesExpectation, bostConnesExpectation, bostConnesExpectation]
  rw [← hf.tsum_add hg]
  apply tsum_congr
  intro n
  ring

/-- Homogeneity of Gibbs expectation. -/
theorem bostConnesExpectation_smul (β c : ℝ) (hβ : 1 < β)
    (f : ℕ+ → ℝ) :
    bostConnesExpectation β hβ (fun n => c * f n) =
      c * bostConnesExpectation β hβ f := by
  rw [bostConnesExpectation, bostConnesExpectation]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Gibbs readback on a singleton indicator observable. -/
theorem expectation_singleton (β : ℝ) (hβ : 1 < β) (n : ℕ+) :
    bostConnesExpectation β hβ
        (Set.indicator ({n} : Set ℕ+) (fun _ => (1 : ℝ))) =
      normalizedBostConnesWeight β n := by
  rw [bostConnesExpectation]
  rw [tsum_eq_single n]
  · simp
  · intro b hb
    simp [Set.indicator, hb]

/-- Alias naming the singleton-indicator Gibbs readback by the expectation API. -/
theorem bostConnesExpectation_indicator_singleton
    (β : ℝ) (hβ : 1 < β) (n : ℕ+) :
    bostConnesExpectation β hβ
        (Set.indicator ({n} : Set ℕ+) (fun _ => (1 : ℝ))) =
      normalizedBostConnesWeight β n :=
  expectation_singleton β hβ n

/-- The normalized Gibbs weights are antitone in the positive-integer index. -/
theorem normalizedWeight_antitone_index (β : ℝ) (hβ : 1 < β) :
    Antitone (normalizedBostConnesWeight β) := by
  intro a b hab
  rw [normalizedBostConnesWeight, normalizedBostConnesWeight]
  refine (div_le_div_iff_of_pos_right (bostConnesPartition_pos β hβ)).2 ?_
  have hβpos : 0 < β := by linarith
  have hpow : ((a : ℕ+) : ℝ) ^ β ≤ ((b : ℕ+) : ℝ) ^ β := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hab) (le_of_lt hβpos)
  have hpos_a : 0 < ((a : ℕ+) : ℝ) ^ β := Real.rpow_pos_of_pos (by positivity) β
  have hpos_b : 0 < ((b : ℕ+) : ℝ) ^ β := Real.rpow_pos_of_pos (by positivity) β
  have hinv : 1 / ((b : ℕ+) : ℝ) ^ β ≤ 1 / ((a : ℕ+) : ℝ) ^ β := by
    exact (one_div_le_one_div hpos_b hpos_a).2 hpow
  simpa [Real.rpow_neg (by positivity : 0 ≤ ((a : ℕ+) : ℝ)) β,
    Real.rpow_neg (by positivity : 0 ≤ ((b : ℕ+) : ℝ)) β] using hinv

/-- The normalized Gibbs weights tend to zero along the positive-integer index. -/
theorem normalizedWeight_tendsto_zero_atTop (β : ℝ) (hβ : 1 < β) :
    Filter.Tendsto (fun n : ℕ+ => normalizedBostConnesWeight β n) Filter.atTop
      (nhds 0) := by
  have hβpos : 0 < β := by linarith
  have hcastNat :
      Filter.Tendsto (fun n : ℕ => ((n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcast :
      Filter.Tendsto (fun n : ℕ+ => ((n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    simpa using hcastNat.comp tendsto_PNat_val_atTop_atTop
  have hpow :
    Filter.Tendsto (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-β)) Filter.atTop
        (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (y := β) hβpos).comp hcast
  have hconst :
    Filter.Tendsto (fun _ : ℕ+ => (bostConnesPartition β)⁻¹) Filter.atTop
        (nhds ((bostConnesPartition β)⁻¹)) := tendsto_const_nhds
  have hmul := hpow.mul hconst
  simpa [normalizedBostConnesWeight, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using hmul

end BostConnesGibbsState
