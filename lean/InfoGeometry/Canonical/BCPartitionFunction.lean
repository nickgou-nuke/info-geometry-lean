import Mathlib
import Mathlib.Analysis.PSeries

open Filter Topology Real Classical

namespace InfoGeometry.Canonical.BCPartitionFunction

/-!
# Bost-Connes KMS Partition Function Divergence at $\beta = 1$

This module formalizes the Bost-Connes partition function $\zeta(\beta)$ as a real-valued
series over inverse temperature $\beta \in \mathbb{R}$ and proves its non-summability (divergence)
at the critical inverse temperature $\beta = 1$.

Key Results:
1. `bcPartitionFunction (β : ℝ)`: The partition function definition $\zeta(\beta) = \sum_{n=1}^\infty n^{-\beta}$.
2. `bc_partition_divergence_at_one`: Proof that $\zeta(1) = \sum_{n=1}^\infty \frac{1}{n}$ is non-summable (harmonic series divergence).
3. `bc_partition_value_at_one`: Evaluation of `bcPartitionFunction 1` to 0.
-/

/-- Bost-Connes partition function as a function of inverse temperature $\beta \in \mathbb{R}$. -/
noncomputable def bcPartitionFunction (β : ℝ) : ℝ :=
  if Summable (fun n : ℕ => (n : ℝ) ^ (-β)) then tsum (fun n : ℕ => (n : ℝ) ^ (-β)) else 0

/-- **Theorem: Non-Summability (Divergence) of Bost-Connes Partition Function at $\beta = 1$**
    At critical inverse temperature $\beta = 1$, the partition function reduces to the
    harmonic series $\sum_{n=1}^\infty \frac{1}{n}$, which is non-summable in $\mathbb{R}$. -/
theorem bc_partition_divergence_at_one :
    ¬ Summable (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) := by
  have h_eq : (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) = (fun n : ℕ => 1 / (n : ℝ)) := by
    ext n
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · rw [rpow_neg_one, inv_eq_one_div]
  rw [h_eq]
  exact not_summable_one_div_natCast

/-- **Theorem: Zero Evaluation at Boundary $\beta = 1$**
    Because the series diverges at $\beta = 1$, `bcPartitionFunction 1` evaluates to 0
    by conditional summation definition. -/
theorem bc_partition_value_at_one :
    bcPartitionFunction 1 = 0 := by
  dsimp [bcPartitionFunction]
  rw [if_neg bc_partition_divergence_at_one]

/-- **Theorem: Summability of Bost-Connes Partition Function for $\beta > 1$**
    For any inverse temperature $\beta > 1$, the $p$-series $\sum_{n=1}^\infty n^{-\beta}$
    converges (is summable in $\mathbb{R}$). -/
theorem bc_partition_summable_above_one {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-β)) := by
  have h_eq : (fun n : ℕ => (n : ℝ) ^ (-β)) = (fun n : ℕ => 1 / (n : ℝ) ^ β) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp only [Nat.cast_zero]
      rw [zero_rpow (by linarith), zero_rpow (by linarith), div_zero]
    · rw [rpow_neg (Nat.cast_nonneg n), inv_eq_one_div]
  rw [h_eq]
  exact Real.summable_one_div_nat_rpow.mpr hβ

end InfoGeometry.Canonical.BCPartitionFunction
