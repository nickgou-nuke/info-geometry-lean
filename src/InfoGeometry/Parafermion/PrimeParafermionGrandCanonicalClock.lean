/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Prime Parafermion Grand Canonical Clock

This module formalizes the finite geometric partition factor $Q_\kappa(x) = \sum_{j=0}^{\kappa-1} x^j$,
Gibbs state probabilities, surprisal decomposition, normalization $\sum_{j=0}^{\kappa-1} p_j = 1$,
and the closed-form grand canonical potential for $\mathbb{Z}_\kappa$ parafermion clocks.

## Mathematical Contract (Three-Bucket Classification)

### BUCKET 1: CLOSED FINITE THEOREMS
- `localParafermionFactor_zero`, `localParafermionFactor_one`, `localParafermionFactor_succ`
- `localParafermionFactor_two`, `localParafermionFactor_three`
- `stateProbability_two`, `stateProbability_three`

### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `localParafermionFactor_eq_quotient`: geometric sum identity $Q_\kappa(x) = \frac{1 - x^\kappa}{1 - x}$ for $x \ne 1$.
- `stateSurprisal_eq_massieu_sub_log_weight`: Gibbs surprisal decomposition $-\log p_n = \Psi_\kappa(x) - n \log x$.
- `sum_stateProbability_eq_one`: exact probability normalization $\sum_{j < \kappa} p_j = 1$ for $Q_\kappa(x) \ne 0$.
- `parafermionGrandPotential_eq_neg_inv_mul_log_quotient`: closed-form grand potential $\Omega_\kappa(x, \beta) = -\beta^{-1} \log \frac{1 - x^\kappa}{1 - x}$ for $x \ne 1$.

### BUCKET 3: OPEN CLOSURE DEBT
- None (`0 sorry`, `0 admit`, `0 custom axioms`, `0 rfl wrappers`).
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Parafermion

/-- Finite geometric partition factor $Q_\kappa(x) = \sum_{j=0}^{\kappa-1} x^j$. -/
def localParafermionFactor (κ : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range κ) (fun j => x ^ j)

/-- Gibbs state probability $p_n = x^n / Q_\kappa(x)$ of the $n$-th parafermion clock mode. -/
def stateProbability (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / localParafermionFactor κ x

/-- Shannon–Gibbs state surprisal $I_n = -\log p_n$. -/
def stateSurprisal (κ : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  -Real.log (stateProbability κ x n)

/-- Massieu free-entropy potential $\Psi_\kappa(x) = \log Q_\kappa(x)$. -/
def parafermionMassieu (κ : ℕ) (x : ℝ) : ℝ :=
  Real.log (localParafermionFactor κ x)

/-- Grand canonical potential $\Omega_\kappa(x, \beta) = -\beta^{-1} \Psi_\kappa(x)$. -/
def parafermionGrandPotential (κ : ℕ) (x β : ℝ) : ℝ :=
  -β⁻¹ * parafermionMassieu κ x

/-- Vanishing of the partition factor at $\kappa = 0$. -/
@[simp]
theorem localParafermionFactor_zero (x : ℝ) :
    localParafermionFactor 0 x = 0 := by
  simp [localParafermionFactor]

/-- Unit partition factor at $\kappa = 1$. -/
@[simp]
theorem localParafermionFactor_one (x : ℝ) :
    localParafermionFactor 1 x = 1 := by
  simp [localParafermionFactor]

/-- One-step recurrence $Q_{\kappa+1}(x) = Q_\kappa(x) + x^\kappa$. -/
theorem localParafermionFactor_succ (κ : ℕ) (x : ℝ) :
    localParafermionFactor (κ + 1) x = localParafermionFactor κ x + x ^ κ := by
  simp [localParafermionFactor, Finset.sum_range_succ]

/-- Closed-form geometric quotient $Q_\kappa(x) = (1 - x^\kappa)/(1 - x)$ for $x \ne 1$. -/
theorem localParafermionFactor_eq_quotient {κ : ℕ} {x : ℝ} (hx : x ≠ 1) :
    localParafermionFactor κ x = (1 - x ^ κ) / (1 - x) := by
  have hmul : localParafermionFactor κ x * (1 - x) = 1 - x ^ κ := by
    simpa [localParafermionFactor, mul_comm, mul_left_comm, mul_assoc] using
      geom_sum_mul_neg x κ
  have hden : (1 - x) ≠ 0 := sub_ne_zero.mpr (by intro h; exact hx h.symm)
  exact (eq_div_iff hden).2 hmul

/-- Binary Majorana partition factor $Q_2(x) = 1 + x$. -/
@[simp]
theorem localParafermionFactor_two (x : ℝ) :
    localParafermionFactor 2 x = 1 + x := by
  simp [localParafermionFactor, Finset.sum_range_succ]

/-- Ternary parafermion partition factor $Q_3(x) = 1 + x + x^2$. -/
@[simp]
theorem localParafermionFactor_three (x : ℝ) :
    localParafermionFactor 3 x = 1 + x + x ^ 2 := by
  simp [localParafermionFactor, Finset.sum_range_succ, pow_two]

/-- Binary mode probability $p_n = x^n / (1 + x)$. -/
@[simp]
theorem stateProbability_two (x : ℝ) (n : ℕ) :
    stateProbability 2 x n = x ^ n / (1 + x) := by
  simp [stateProbability]

/-- Ternary mode probability $p_n = x^n / (1 + x + x^2)$. -/
@[simp]
theorem stateProbability_three (x : ℝ) (n : ℕ) :
    stateProbability 3 x n = x ^ n / (1 + x + x ^ 2) := by
  simp [stateProbability]

/-- Exact decomposition of state surprisal into the Massieu potential minus $n \log x$. -/
theorem stateSurprisal_eq_massieu_sub_log_weight
    {κ : ℕ} {x : ℝ} (n : ℕ)
    (hx : 0 < x) (hQ : 0 < localParafermionFactor κ x) :
    stateSurprisal κ x n =
      parafermionMassieu κ x - n * Real.log x := by
  unfold stateSurprisal stateProbability parafermionMassieu
  rw [Real.log_div (pow_pos hx n).ne' hQ.ne', Real.log_pow x n]
  ring

/-- Exact normalization of the Gibbs state probabilities over $\mathrm{range}\,\kappa$. -/
theorem sum_stateProbability_eq_one
    {κ : ℕ} {x : ℝ} (hQ : localParafermionFactor κ x ≠ 0) :
    Finset.sum (Finset.range κ) (fun n => stateProbability κ x n) = 1 := by
  unfold stateProbability
  rw [← Finset.sum_div]
  exact div_self hQ

/-- Closed-form grand canonical potential $\Omega_\kappa(x, \beta) = -\beta^{-1} \log \frac{1 - x^\kappa}{1 - x}$ for $x \ne 1$. -/
theorem parafermionGrandPotential_eq_neg_inv_mul_log_quotient
    {κ : ℕ} {x : ℝ} (β : ℝ) (hx : x ≠ 1) :
    parafermionGrandPotential κ x β =
      -β⁻¹ * Real.log ((1 - x ^ κ) / (1 - x)) := by
  unfold parafermionGrandPotential parafermionMassieu
  rw [localParafermionFactor_eq_quotient hx]

end InfoGeometry.Parafermion
