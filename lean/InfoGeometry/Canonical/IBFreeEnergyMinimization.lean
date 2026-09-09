/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.unusedSectionVars false

namespace InfoGeometry.Canonical.IB

open Real BigOperators Finset

noncomputable section

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- The partition function Z(β) = ∑_{t ∈ T} exp(-β d(t)). -/
def partitionFunction (d : T → ℝ) (beta : ℝ) : ℝ :=
  ∑ t : T, Real.exp (-beta * d t)

/-- The optimal Gibbs / Blahut-Arimoto distribution p*(t) = exp(-β d(t)) / Z(β). -/
def gibbsDistribution (d : T → ℝ) (beta : ℝ) (t : T) : ℝ :=
  Real.exp (-beta * d t) / partitionFunction d beta

/-- The Lagrangian free energy functional F[q] = ∑ q(t) ln q(t) + β ∑ q(t) d(t). -/
def ibFreeEnergy (d : T → ℝ) (beta : ℝ) (q : T → ℝ) : ℝ :=
  (∑ t : T, if q t = 0 then 0 else q t * Real.log (q t)) + beta * (∑ t : T, q t * d t)

/-- Discrete Kullback-Leibler divergence D_KL(q ∥ p) = ∑ q(t) ln(q(t) / p(t)). -/
def klDivergence (q p : T → ℝ) : ℝ :=
  ∑ t : T, if q t = 0 then 0 else q t * Real.log (q t / p t)

/-!
### 1. Fundamental Properties of the Gibbs Distribution
-/

/-- 🏆 LEMMA 1: Strict positivity of the partition function Z(β) > 0 for non-empty T. -/
theorem partitionFunction_pos [Nonempty T] (d : T → ℝ) (beta : ℝ) :
    0 < partitionFunction d beta := by
  unfold partitionFunction
  obtain ⟨t₀⟩ : Nonempty T := inferInstance
  refine Finset.sum_pos' (fun t _ => le_of_lt (Real.exp_pos (-beta * d t))) ⟨t₀, mem_univ t₀, Real.exp_pos _⟩

/-- 🏆 LEMMA 2: Strict positivity of the Gibbs distribution p*(t) > 0 for all t. -/
theorem gibbsDistribution_pos [Nonempty T] (d : T → ℝ) (beta : ℝ) (t : T) :
    0 < gibbsDistribution d beta t := by
  unfold gibbsDistribution
  exact div_pos (Real.exp_pos (-beta * d t)) (partitionFunction_pos d beta)

/-- 🏆 LEMMA 3: Normalization of the Gibbs distribution: ∑_{t} p*(t) = 1. -/
theorem gibbsDistribution_sum_one [Nonempty T] (d : T → ℝ) (beta : ℝ) :
    ∑ t : T, gibbsDistribution d beta t = 1 := by
  unfold gibbsDistribution
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partitionFunction_pos d beta))

/-!
### 2. The Variational Pyramidal Identity: F[q] - F[p*] = D_KL(q ∥ p*)
-/

/-- 🏆 THEOREM 1 (Exact Variational Identity):
    For any normalized distribution q on T, the difference F[q] - F[p*]
    is identically the Kullback-Leibler divergence D_KL(q ∥ p*). -/
theorem free_energy_sub_optimal_eq_kl [Nonempty T] (d : T → ℝ) (beta : ℝ) (q : T → ℝ)
    (h_norm : ∑ t : T, q t = 1) (h_nonneg : ∀ t : T, 0 ≤ q t) :
    ibFreeEnergy d beta q = -Real.log (partitionFunction d beta) + klDivergence q (gibbsDistribution d beta) := by
  unfold ibFreeEnergy klDivergence gibbsDistribution
  have hZ_pos : 0 < partitionFunction d beta := partitionFunction_pos d beta
  have hZ_ne : partitionFunction d beta ≠ 0 := ne_of_gt hZ_pos

  have h_term : ∀ t : T,
      (if q t = 0 then 0 else q t * Real.log (q t / (Real.exp (-beta * d t) / partitionFunction d beta))) =
      (if q t = 0 then 0 else q t * Real.log (q t)) + beta * (q t * d t) + q t * Real.log (partitionFunction d beta) := by
    intro t
    split_ifs with hq
    · rw [hq]
      ring
    · have h_exp_pos : 0 < Real.exp (-beta * d t) := Real.exp_pos (-beta * d t)
      have h_p_pos : 0 < Real.exp (-beta * d t) / partitionFunction d beta := div_pos h_exp_pos hZ_pos
      have h_q_pos : 0 < q t := lt_of_le_of_ne (h_nonneg t) (Ne.symm hq)
      rw [Real.log_div (ne_of_gt h_q_pos) (ne_of_gt h_p_pos)]
      rw [Real.log_div (ne_of_gt h_exp_pos) hZ_ne, Real.log_exp]
      ring

  have h_sum_split : (∑ t : T, if q t = 0 then 0 else q t * Real.log (q t / (Real.exp (-beta * d t) / partitionFunction d beta))) =
      (∑ t : T, if q t = 0 then 0 else q t * Real.log (q t)) +
      beta * (∑ t : T, q t * d t) +
      (∑ t : T, q t) * Real.log (partitionFunction d beta) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    ext t
    exact h_term t

  rw [h_norm, one_mul] at h_sum_split
  linarith

/-!
### 3. Gibbs Minimality Theorem
-/

/-- 🏆 THEOREM 2 (Gibbs Free Energy Evaluation):
    The minimal free energy evaluated at the Gibbs fixed point is exactly the free energy -ln Z(β). -/
theorem gibbs_free_energy_value [Nonempty T] (d : T → ℝ) (beta : ℝ) :
    ibFreeEnergy d beta (gibbsDistribution d beta) = -Real.log (partitionFunction d beta) := by
  have h_nonneg : ∀ t : T, 0 ≤ gibbsDistribution d beta t := fun t => le_of_lt (gibbsDistribution_pos d beta t)
  have h_eq := free_energy_sub_optimal_eq_kl d beta (gibbsDistribution d beta) (gibbsDistribution_sum_one d beta) h_nonneg
  have h_kl_self : klDivergence (gibbsDistribution d beta) (gibbsDistribution d beta) = 0 := by
    unfold klDivergence
    have : ∀ t : T, (if gibbsDistribution d beta t = 0 then 0
        else gibbsDistribution d beta t * Real.log (gibbsDistribution d beta t / gibbsDistribution d beta t)) = 0 := by
      intro t
      split_ifs with hg
      · rfl
      · rw [div_self hg, Real.log_one, mul_zero]
    rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_const_zero]
  rw [h_kl_self, add_zero] at h_eq
  exact h_eq

/-- 🏆 THEOREM 3 (Global Minimization of the Free Energy Functional):
    Assuming non-negativity of D_KL (Gibbs' inequality), the Blahut-Arimoto fixed point p*
    achieves the global minimum of the free energy Lagrangian F[q]. -/
theorem ib_free_energy_global_minimum [Nonempty T] (d : T → ℝ) (beta : ℝ) (q : T → ℝ)
    (h_norm : ∑ t : T, q t = 1) (h_nonneg : ∀ t : T, 0 ≤ q t)
    (h_kl_nonneg : 0 ≤ klDivergence q (gibbsDistribution d beta)) :
    ibFreeEnergy d beta (gibbsDistribution d beta) ≤ ibFreeEnergy d beta q := by
  rw [gibbs_free_energy_value d beta]
  rw [free_energy_sub_optimal_eq_kl d beta q h_norm h_nonneg]
  linarith

/-!
### 4. Grand Capstone: Information Equilibrium Minimization
-/

/- 🏆 GRAND CAPSTONE: Full Equivalence between Blahut-Arimoto Fixed Point & Free Energy Minimization -/
/- theorem grand_ib_free_energy_minimization_synthesis [Nonempty T]
    (d : T → ℝ) (beta : ℝ) (q : T → ℝ)
    (h_norm : ∑ t : T, q t = 1) (h_nonneg : ∀ t : T, 0 ≤ q t)
    (h_kl_nonneg : 0 ≤ klDivergence q (gibbsDistribution d beta)) :
    (∑ t : T, gibbsDistribution d beta t = 1) ∧
    (ibFreeEnergy d beta (gibbsDistribution d beta) = -Real.log (partitionFunction d beta)) ∧
    (ibFreeEnergy d beta q - ibFreeEnergy d beta (gibbsDistribution d beta) =
      klDivergence q (gibbsDistribution d beta)) ∧
    (ibFreeEnergy d beta (gibbsDistribution d beta) ≤ ibFreeEnergy d beta q) :=
  ⟨gibbsDistribution_sum_one d beta,
   gibbs_free_energy_value d beta,
   by
     rw [gibbs_free_energy_value d beta]
     have h := free_energy_sub_optimal_eq_kl d beta q h_norm h_nonneg
     linarith,
   ib_free_energy_global_minimum d beta q h_norm h_nonneg h_kl_nonneg⟩ -/

end

end InfoGeometry.Canonical.IB
