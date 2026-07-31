import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.SPG.PrimeRegisterBudgetLowerBound

namespace Omega.SPG

/-- For a fixed finite-state prime-register scheme, the distinguishable fraction is bounded by a
constant numerator over the full fiber size `p ^ r(f)` and therefore tends to `0` once
    `r(f) → ∞`.
    cor:spg-prime-register-distinguishable-fraction-vanishes -/
theorem paper_spg_prime_register_distinguishable_fraction_vanishes
    (p k E : ℕ) (hp_prime : p.Prime)
    (residualRank : ℕ → ℕ) (distinguishableFraction : ℕ → ℝ)
    (h_nonneg : ∀ n, 0 ≤ distinguishableFraction n)
    (h_le_budget_ratio :
      ∀ n, distinguishableFraction n ≤ ((E + 1 : ℝ) ^ k) / (p : ℝ) ^ residualRank n)
    (h_residualRankGrows : Filter.Tendsto residualRank Filter.atTop Filter.atTop) :
    Filter.Tendsto distinguishableFraction Filter.atTop (nhds 0) := by
  letI : Fact p.Prime := ⟨hp_prime⟩
  have hp : 1 < (p : ℝ) := by
    exact_mod_cast hp_prime.one_lt
  have hdenom :
      Filter.Tendsto (fun n => (p : ℝ) ^ residualRank n) Filter.atTop Filter.atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt hp).comp h_residualRankGrows
  have hratio :
      Filter.Tendsto
        (fun n => ((E + 1 : ℝ) ^ k) / (p : ℝ) ^ residualRank n)
        Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hdenom
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
    h_nonneg h_le_budget_ratio

end Omega.SPG
