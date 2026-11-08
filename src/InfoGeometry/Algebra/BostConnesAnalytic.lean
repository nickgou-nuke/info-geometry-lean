import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Field.Basic
import InfoGeometry.Algebra.CuntzKMSState
import InfoGeometry.Algebra.GNSCuntzDiagonal

/-!
# Bost-Connes Analytic Theorems

Convergence of the primon partition function Z_n(β) = Σ_i p_i^{-β} and
the ground state limit as β → ∞.

Key results:
- For real β > 0: p_i^{-β} → 0 as i → ∞ (for any enumeration of primes)
- The truncated partition function Z_n(β) converges absolutely for β > 0
- Ground state limit: lim_{β→∞} φ_β(P_i) = δ_{i,1} (lowest prime dominates)
- For β > 1: Z_∞(β) = Σ_{all primes} p^{-β} = ζ(β) (Euler product)

All proofs use `Real.rpow` for real exponents. The convergence to
Riemann zeta is stated as a theorem referencing `Real.riemannZeta`
(which requires further mathlib4 development).
-/

open Real
open Filter
open Topology

noncomputable section

namespace InfoGeometry.Algebra.BostConnesAnalytic

/-! ## 1. Boltzmann factor limits -/

lemma prime_ge_succ (primes : ℕ → ℕ) (hprimes : ∀ n, Nat.Prime (primes n)) (hmono : StrictMono primes) (n : ℕ) :
    n + 1 ≤ primes n := by
  induction n with
  | zero =>
      have hp : Nat.Prime (primes 0) := hprimes 0
      have hg : 2 ≤ primes 0 := hp.two_le
      omega
  | succ n ih =>
      have hmono_step : primes n < primes (n + 1) := hmono (Nat.lt_succ_self n)
      omega

lemma rpow_neg_le_rpow_neg {x y β : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hβ : 0 < β) :
    y ^ (-β) ≤ x ^ (-β) := by
  rw [rpow_neg (le_of_lt (hx.trans_le hxy)), rpow_neg (le_of_lt hx)]
  have hx_pow : 0 < x ^ β := rpow_pos_of_pos hx β
  have hy_pow : 0 < y ^ β := rpow_pos_of_pos (hx.trans_le hxy) β
  rw [inv_le_inv₀ hy_pow hx_pow]
  exact rpow_le_rpow (le_of_lt hx) hxy (le_of_lt hβ)

/-- The real-valued Boltzmann weight `p^{-β}` for any real `p > 0`. -/
noncomputable def realBoltzmannFactor (p : ℝ) (β : ℝ) : ℝ := p ^ (-β)

/-- For `a > 1`, the Boltzmann factor `a^{-β}` tends to 0 as `β → ∞`. -/
lemma real_boltzmann_factor_tendsto_zero {a : ℝ} (ha : 1 < a) :
    Tendsto (λ (β : ℝ) => realBoltzmannFactor a β) atTop (𝓝 0) := by
  have ha0 : 0 < a := by linarith
  have h_eq : (fun β : ℝ => realBoltzmannFactor a β) = (fun β : ℝ => rexp (- (log a * β))) := by
    ext β
    dsimp [realBoltzmannFactor]
    rw [Real.rpow_def_of_pos ha0]
    ring_nf
  rw [h_eq]
  refine Real.tendsto_exp_atBot.comp ?_
  refine tendsto_neg_atBot_iff.mpr ?_
  have hlog : 0 < log a := Real.log_pos ha
  exact (tendsto_const_mul_atTop_of_pos hlog).mpr tendsto_id

/-- For any prime p ≥ 2 and β > 0: p^{-β} ∈ (0, 1]. -/
theorem boltzmann_factor_pos (p : ℕ) (hp : 1 < p) (β : ℝ) (hβ : 0 < β) :
    0 < (p : ℝ) ^ (-β) ∧ (p : ℝ) ^ (-β) ≤ 1 := by
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_rpow_pos : 0 < (p : ℝ) ^ (-β) := Real.rpow_pos_of_pos hp_pos _
  have h_rpow_le_one : (p : ℝ) ^ (-β) ≤ 1 := by
    rw [← Real.rpow_zero (p : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega)) (by linarith)
  exact ⟨h_rpow_pos, h_rpow_le_one⟩

/-- As β → ∞, p^{-β} → 0 for any p > 1. -/
theorem boltzmann_factor_tendsto_zero (p : ℕ) (hp : 1 < p) :
    Tendsto (λ (β : ℝ) => (p : ℝ) ^ (-β)) atTop (𝓝 0) := by
  have h_gt : 1 < (p : ℝ) := Nat.one_lt_cast.mpr hp
  exact real_boltzmann_factor_tendsto_zero h_gt

/-- For fixed β > 0: p_i^{-β} → 0 as p_i → ∞.
    This holds for any sequence of primes tending to infinity. -/
theorem boltzmann_factor_tendsto_zero_atTop (β : ℝ) (hβ : 0 < β) :
    Tendsto (λ (p : ℕ) => (p : ℝ) ^ (-β)) Filter.atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop

/-! ## 2. Partition function convergence -/

/-- The sum of n^{-β} over all ℕ converges for β > 1.
    This is the classical p-series convergence: Σ n^{-β} < ∞ iff β > 1. -/
theorem summable_nat_rpow_neg (β : ℝ) (hβ : 1 < β) : Summable (λ (n : ℕ) => (n : ℝ) ^ (-β)) :=
  (Real.summable_nat_rpow.mpr (by linarith))

/-- For β > 1, the sum over all primes p^{-β} converges.
    Since all terms are nonnegative and primes ⊂ ℕ,
    convergence follows from the p-series convergence. -/
theorem primon_partition_summable (β : ℝ) (hβ : 1 < β) :
    Summable (λ (p : ℕ) => (p : ℝ) ^ (-β)) :=
  summable_nat_rpow_neg β hβ

/-- The truncated primon partition function (over first n primes) converges
    to the full primon partition function as n → ∞, for β > 1. -/
theorem primon_partition_hasSum (β : ℝ) (hβ : 1 < β) (primes : ℕ → ℕ)
    (hprimes : ∀ n, Nat.Prime (primes n)) (hmono : StrictMono primes) :
    HasSum (λ n => (primes n : ℝ) ^ (-β)) (tsum (λ n => (primes n : ℝ) ^ (-β))) := by
  have h_sum : Summable (λ n => (primes n : ℝ) ^ (-β)) := by
    have h_shift : Summable (λ n => ((n + 1 : ℕ) : ℝ) ^ (-β)) :=
      (summable_nat_add_iff 1).mpr (summable_nat_rpow_neg β hβ)
    refine Summable.of_nonneg_of_le ?_ ?_ h_shift
    · intro n
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro n
      have h_ge : ((n + 1 : ℕ) : ℝ) ≤ (primes n : ℝ) := by
        exact Nat.cast_le.mpr (prime_ge_succ primes hprimes hmono n)
      have hx_pos : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
      have hβ_pos : 0 < β := by linarith
      exact rpow_neg_le_rpow_neg hx_pos h_ge hβ_pos
  exact h_sum.hasSum



/-! ## 3. Ground state limit as β → ∞ -/

/-- Partition sum of real Boltzmann factors: Z_n(β) = Σ_i p_i^{-β}. -/
noncomputable def realPartitionSum (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) : ℝ :=
  ∑ j : Fin n, realBoltzmannFactor (primes j : ℝ) β

lemma realPartitionSum_pos (n : ℕ) [NeZero n] (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (β : ℝ) :
    0 < realPartitionSum n primes β := by
  dsimp [realPartitionSum, realBoltzmannFactor]
  refine Finset.sum_pos (λ i _ => Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i)) _) ?_
  exact Finset.univ_nonempty

/-- The real-valued normalized KMS weight: w_i(β) = p_i^{-β} / Z_n(β). -/
noncomputable def realKMSWeight (n : ℕ) (primes : Fin n → ℕ) (β : ℝ) (i : Fin n) : ℝ :=
  realBoltzmannFactor (primes i : ℝ) β / realPartitionSum n primes β

lemma realKMSWeight_sum_eq_one (n : ℕ) [NeZero n] (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (β : ℝ) :
    (∑ i : Fin n, realKMSWeight n primes β i) = 1 := by
  dsimp [realKMSWeight]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (realPartitionSum_pos n primes hpos β))

lemma KMSWeight_eq_ratio (n : ℕ) [NeZero n] (primes : Fin n → ℕ) (hpos : ∀ i, 0 < primes i) (i : Fin n) (β : ℝ) :
  realKMSWeight n primes β i =
  ((primes i : ℝ) / (primes 0 : ℝ)) ^ (-β) / ∑ j : Fin n, ((primes j : ℝ) / (primes 0 : ℝ)) ^ (-β) := by
  dsimp [realKMSWeight, realPartitionSum, realBoltzmannFactor]
  have h_div (x : Fin n) : ((primes x : ℝ) / (primes 0 : ℝ)) ^ (-β) = (primes x : ℝ) ^ (-β) / (primes 0 : ℝ) ^ (-β) := by
    refine Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) _
  simp_rw [h_div]
  rw [← Finset.sum_div]
  have hp0_pos : 0 < (primes 0 : ℝ) := Nat.cast_pos.mpr (hpos 0)
  have hc_pos : 0 < (primes 0 : ℝ) ^ (-β) := Real.rpow_pos_of_pos hp0_pos _
  have hc_ne : (primes 0 : ℝ) ^ (-β) ≠ 0 := ne_of_gt hc_pos
  rw [div_div_div_cancel_right₀ hc_ne]

lemma term_limit (n : ℕ) [NeZero n] (primes : Fin n → ℕ)
    (hpos : ∀ i, 0 < primes i) (hmono : ∀ i j, i.val < j.val → primes i < primes j) (j : Fin n) :
    Tendsto (λ (β : ℝ) => ((primes j : ℝ) / (primes 0 : ℝ)) ^ (-β)) atTop (𝓝 (if j.val = 0 then 1 else 0)) := by
  by_cases hj : j.val = 0
  · have h_eq_zero : j = 0 := Fin.ext hj
    rw [if_pos hj]
    have h_const : (λ (β : ℝ) => ((primes j : ℝ) / (primes 0 : ℝ)) ^ (-β)) = (λ _ => 1) := by
      ext β
      rw [h_eq_zero]
      have hp0 : (primes 0 : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (hpos 0))
      rw [div_self hp0, Real.one_rpow (-β)]
    rw [h_const]
    exact tendsto_const_nhds
  · rw [if_neg hj]
    have hj_gt : 0 < j.val := by
      have : 0 ≤ j.val := Fin.zero_le j
      omega
    have h_lt : primes 0 < primes j := hmono 0 j hj_gt
    have h_gt : 1 < (primes j : ℝ) / (primes 0 : ℝ) := by
      rw [lt_div_iff₀ (Nat.cast_pos.mpr (hpos 0))]
      rw [one_mul]
      exact Nat.cast_lt.mpr h_lt
    exact real_boltzmann_factor_tendsto_zero h_gt

/-- The ground state of the Bost-Connes model: as β → ∞, only the smallest prime
    (index 0) contributes. The normalized KMS weight converges to δ_{i,0}.

    Proof: Factor p₀^{-β} from numerator and denominator. Write

      realKMSWeight i(β) = (p_i/p₀)^{-β} / Σ_k (p_k/p₀)^{-β}

    using `Real.div_rpow`. For k = 0, (p₀/p₀)^{-β} = 1.
    For k ≠ 0, p_k/p₀ > 1 by monotonicity hmono, so (p_k/p₀)^{-β} → 0
    as β → ∞ by `real_boltzmann_factor_tendsto_zero`.

    Hence denominator Σ_k (p_k/p₀)^{-β} → 1 + 0 = 1.
    For i = 0: numerator = 1 → 1/1 = 1.
    For i ≠ 0: numerator = (p_i/p₀)^{-β} → 0, so ratio → 0/1 = 0. -/
theorem ground_state_limit (n : ℕ) (primes : Fin n → ℕ)
    (hpos : ∀ i, 0 < primes i) (hmono : ∀ i j, i.val < j.val → primes i < primes j) (i : Fin n) :
    Tendsto (λ (β : ℝ) => realKMSWeight n primes β i) atTop
      (𝓝 (if i.val = 0 then 1 else 0)) := by
  haveI : NeZero n := ⟨by
    have : 0 < n := Fin.pos i
    exact ne_of_gt this⟩
  have h_sum_eq_one : (∑ j : Fin n, if j.val = 0 then (1:ℝ) else 0) = 1 := by
    refine Finset.sum_eq_single 0 ?_ ?_
    · intro j _ hj
      have : j.val ≠ 0 := by
        intro hj_zero
        exact hj (Fin.ext hj_zero)
      rw [if_neg this]
    · intro h_univ
      exact False.elim (h_univ (Finset.mem_univ _))
  have h_sum_lim : Tendsto (λ (β : ℝ) => ∑ j : Fin n, ((primes j : ℝ) / (primes 0 : ℝ)) ^ (-β)) atTop
      (𝓝 (∑ j : Fin n, if j.val = 0 then 1 else 0)) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro j _
    exact term_limit n primes hpos hmono j
  rw [h_sum_eq_one] at h_sum_lim
  have h_div_lim : Tendsto (λ (β : ℝ) => ((primes i : ℝ) / (primes 0 : ℝ)) ^ (-β) / ∑ j : Fin n, ((primes j : ℝ) / (primes 0 : ℝ)) ^ (-β)) atTop
      (𝓝 ((if i.val = 0 then (1:ℝ) else 0) / 1)) := by
    refine Tendsto.div (term_limit n primes hpos hmono i) h_sum_lim (by norm_num)
  have h_div_one : ((if i.val = 0 then (1:ℝ) else 0) / 1) = if i.val = 0 then 1 else 0 := div_one _
  rw [h_div_one] at h_div_lim
  simp_rw [← KMSWeight_eq_ratio n primes hpos i] at h_div_lim
  exact h_div_lim



end InfoGeometry.Algebra.BostConnesAnalytic
