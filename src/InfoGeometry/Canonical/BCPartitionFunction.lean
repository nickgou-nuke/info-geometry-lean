import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.PSeries
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Filter Topology Real Classical
open scoped ENNReal

namespace InfoGeometry.Canonical.BCPartitionFunction

/-!
# Extended Dirichlet partition sum and its convergence boundary

This module formalizes the Dirichlet Boltzmann sum as an `ℝ≥0∞`-valued tsum.
The extended nonnegative reals represent divergence by `∞`; they do not replace
it with an arbitrary real sentinel. The results here establish the harmonic
boundary and convergence for `β > 1`. They do not construct a Bost--Connes
`C*`-dynamical system, a Gibbs/KMS state, or its operator trace.

Key Results:
1. `dirichletBoltzmannSeries (β : ℝ)`: the extended sum of weights `n^(-β)`.
2. `dirichlet_powerSeries_not_summable_at_one`: harmonic-series divergence.
3. `dirichletBoltzmannSeries_at_one`: the extended sum is `∞` at `β = 1`.
4. For `β > 1`, the extended sum is the `ENNReal.ofReal` of the real tsum.
-/

/-- Extended Dirichlet Boltzmann sum. Divergence is represented by `∞`. -/
noncomputable def dirichletBoltzmannSeries (β : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (-β))

/-- The real Dirichlet weight series is not summable at the harmonic boundary. -/
theorem dirichlet_powerSeries_not_summable_at_one :
    ¬ Summable (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) := by
  have h_eq : (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) = (fun n : ℕ => 1 / (n : ℝ)) := by
    ext n
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · rw [rpow_neg_one, inv_eq_one_div]
  rw [h_eq]
  exact not_summable_one_div_natCast

/-- At the harmonic boundary the extended Dirichlet sum diverges to `∞`. -/
theorem dirichletBoltzmannSeries_at_one :
    dirichletBoltzmannSeries 1 = ⊤ := by
  by_contra h
  have hfinite :
      (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (-1 : ℝ))) ≠ ⊤ := by
    simpa [dirichletBoltzmannSeries] using h
  have hsum : Summable (fun n : ℕ =>
      (ENNReal.ofReal ((n : ℝ) ^ (-1 : ℝ))).toReal) :=
    ENNReal.summable_toReal hfinite
  have hterms : (fun n : ℕ =>
      (ENNReal.ofReal ((n : ℝ) ^ (-1 : ℝ))).toReal) =
        (fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) := by
    funext n
    rw [ENNReal.toReal_ofReal]
    positivity
  apply dirichlet_powerSeries_not_summable_at_one
  exact hsum.congr (fun n => congrFun hterms n)

/-- The real Dirichlet weight series converges for `β > 1`. -/
theorem dirichlet_powerSeries_summable_above_one {β : ℝ} (hβ : 1 < β) :
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

/-- Above the convergence boundary, the extended sum is the real Dirichlet
series embedded into `ℝ≥0∞`. -/
theorem dirichletBoltzmannSeries_eq_ofReal_tsum {β : ℝ} (hβ : 1 < β) :
    dirichletBoltzmannSeries β =
      ENNReal.ofReal (∑' n : ℕ, (n : ℝ) ^ (-β)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (f := fun n : ℕ => (n : ℝ) ^ (-β))
    (fun n => by positivity)
    (dirichlet_powerSeries_summable_above_one hβ)).symm

end InfoGeometry.Canonical.BCPartitionFunction
