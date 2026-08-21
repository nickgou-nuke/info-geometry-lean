import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# KMS Thermodynamic Identity and the Variational Free Energy Principle

This module formalizes:
1. The Gibbs/KMS Partition Function: Z(K) = ∑_i exp(-K_i).
2. The Massieu–Planck / Helmholtz Free Energy: F(K) = - log Z(K).
3. The Internal Energy: E(K) = ∑_i p_i * K_i.
4. The von Neumann / Gibbs Entropy: S(K) = - ∑_i p_i * log(p_i).
5. THEOREM 1 (Fundamental Thermodynamic Identity): F(K) = E(K) - S(K).
6. THEOREM 2 (Variational Principle / Free Energy Minimum):
     For any probability distribution q: F(K) ≤ E_q - S(q)
     derived directly from Klein's relative entropy inequality D_KL(q ∥ p) ≥ 0.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.InformationGeometry.KMS

/-!
=============================================================================
PART 1: The Gibbs Partition Function and Equilibrium State
=============================================================================
-/

/-- The Gibbs/KMS Partition Function: Z(K) = ∑_i exp(-K_i). -/
def partitionZ {ι : Type*} [Fintype ι] (K : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-K i)

/-- Strict positivity of the partition function. -/
theorem partitionZ_pos {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) : 0 < partitionZ K := by
  dsimp [partitionZ]
  exact sum_pos (fun i _ => Real.exp_pos (-K i)) univ_nonempty

/-- The Equilibrium Gibbs/KMS Probability State: p_i = exp(-K_i) / Z(K). -/
def gibbsProb {ι : Type*} [Fintype ι] (K : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (-K i) / partitionZ K

/-- Strict positivity of the equilibrium Gibbs probabilities. -/
theorem gibbsProb_pos {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) (i : ι) : 0 < gibbsProb K i := by
  dsimp [gibbsProb]
  exact div_pos (Real.exp_pos (-K i)) (partitionZ_pos K)

/-- Normalization of the Gibbs state: ∑_i p_i = 1. -/
@[simp]
theorem gibbsProb_sum_one {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) : ∑ i, gibbsProb K i = 1 := by
  dsimp [gibbsProb]
  rw [← sum_div]
  exact div_self (ne_of_gt (partitionZ_pos K))

/-!
=============================================================================
PART 2: Free Energy, Internal Energy, and the Identity F = E - S
=============================================================================
-/

/-- The Massieu–Planck / Helmholtz Free Energy: F(K) = - log Z(K). -/
def freeEnergy {ι : Type*} [Fintype ι] (K : ι → ℝ) : ℝ :=
  - Real.log (partitionZ K)

/-- The Internal Energy Expectation: E(K) = ∑_i p_i * K_i. -/
def internalEnergy {ι : Type*} [Fintype ι] (K : ι → ℝ) : ℝ :=
  ∑ i, gibbsProb K i * K i

/-- The Gibbs/von Neumann Entropy: S(K) = - ∑_i p_i * log(p_i). -/
def gibbsEntropy {ι : Type*} [Fintype ι] (K : ι → ℝ) : ℝ :=
  - ∑ i, gibbsProb K i * Real.log (gibbsProb K i)

/-- 
  MASTER THEOREM 1 (The Fundamental Thermodynamic Identity F = E - S):
  F(K) = E(K) - S(K)
-/
theorem free_energy_eq_energy_sub_entropy {ι : Type*} [Fintype ι] [Nonempty ι] (K : ι → ℝ) :
    freeEnergy K = internalEnergy K - gibbsEntropy K := by
  dsimp [gibbsEntropy, internalEnergy, freeEnergy, gibbsProb]
  have h_log_p (i : ι) :
      Real.log (Real.exp (-K i) / partitionZ K) = -K i - Real.log (partitionZ K) := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos (-K i))) (ne_of_gt (partitionZ_pos K))]
    rw [Real.log_exp]
  have h_sum_entropy :
      (∑ i, (Real.exp (-K i) / partitionZ K) * Real.log (Real.exp (-K i) / partitionZ K)) =
        (∑ i, (Real.exp (-K i) / partitionZ K) * (-K i)) - Real.log (partitionZ K) := by
    simp_rw [h_log_p, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h_p_sum : (∑ i, Real.exp (-K i) / partitionZ K) = 1 := by
      rw [← sum_div]
      exact div_self (ne_of_gt (partitionZ_pos K))
    rw [h_p_sum, one_mul]
  have h_entropy_eval :
      - (∑ i, (Real.exp (-K i) / partitionZ K) * Real.log (Real.exp (-K i) / partitionZ K)) =
        (∑ i, (Real.exp (-K i) / partitionZ K) * K i) + Real.log (partitionZ K) := by
    rw [h_sum_entropy]
    have h_neg_k (i : ι) : (Real.exp (-K i) / partitionZ K) * (-K i) = - ((Real.exp (-K i) / partitionZ K) * K i) := by ring
    simp_rw [h_neg_k, sum_neg_distrib]
    ring
  rw [h_entropy_eval]
  ring

/-!
=============================================================================
PART 3: The Variational Principle (Free Energy Minimization)
=============================================================================
-/

/-- Standard lower bound for the natural logarithm: 1 - 1/x ≤ log x for x > 0. -/
lemma log_bound (x : ℝ) (hx : 0 < x) :
    1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-- 
  MASTER THEOREM 2 (The Variational Principle of Statistical Mechanics):
  For ANY normalized probability distribution q on ι:
    F(K) ≤ ∑_i q_i * K_i - (- ∑_i q_i * log(q_i))
  proving that the physical free energy is the absolute minimum of the
  non-equilibrium free energy functional: F(K) = min_q (E_q - S_q).
-/
theorem variational_free_energy_principle
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → ℝ) (q : ι → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i, q i = 1) :
    freeEnergy K ≤ (∑ i, q i * K i) - (- ∑ i, q i * Real.log (q i)) := by
  -- Let p be the equilibrium Gibbs distribution
  let p := gibbsProb K
  have hp_pos (i : ι) : 0 < p i := gibbsProb_pos K i
  have hp_sum : ∑ i, p i = 1 := gibbsProb_sum_one K

  -- Klein's inequality: D_KL(q ∥ p) ≥ 0
  have h_term_ge (i : ι) :
      q i * (1 - p i / q i) ≤ q i * Real.log (q i / p i) := by
    have h_ratio : 0 < q i / p i := div_pos (hq_pos i) (hp_pos i)
    have h_log := log_bound (q i / p i) h_ratio
    have h_inv : (q i / p i)⁻¹ = p i / q i := inv_div (q i) (p i)
    rw [h_inv] at h_log
    nlinarith [le_of_lt (hq_pos i)]
  
  have h_sum_ge : ∑ i, q i * (1 - p i / q i) ≤ ∑ i, q i * Real.log (q i / p i) :=
    sum_le_sum (fun i _ => h_term_ge i)

  have h_lhs_zero : ∑ i, q i * (1 - p i / q i) = 0 := by
    calc
      ∑ i, q i * (1 - p i / q i) = ∑ i, (q i - q i * (p i / q i)) := by
        apply sum_congr rfl; intro i _; ring
      _ = ∑ i, (q i - p i) := by
        apply sum_congr rfl; intro i _
        rw [mul_div_cancel₀ (p i) (ne_of_gt (hq_pos i))]
      _ = (∑ i, q i) - (∑ i, p i) := by rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [hq_sum, hp_sum]
      _ = 0 := sub_self 1

  rw [h_lhs_zero] at h_sum_ge

  -- Expand D_KL(q ∥ p) = ∑ q_i * log(q_i / p_i) = - S_q + E_q - F
  have h_expand (i : ι) :
      q i * Real.log (q i / p i) = q i * Real.log (q i) + q i * K i + q i * Real.log (partitionZ K) := by
    have h_p_val : p i = Real.exp (-K i) / partitionZ K := rfl
    have h_p_pos : 0 < Real.exp (-K i) / partitionZ K := div_pos (Real.exp_pos (-K i)) (partitionZ_pos K)
    rw [h_p_val]
    rw [Real.log_div (ne_of_gt (hq_pos i)) (ne_of_gt h_p_pos)]
    rw [Real.log_div (ne_of_gt (Real.exp_pos (-K i))) (ne_of_gt (partitionZ_pos K))]
    rw [Real.log_exp]
    ring

  simp_rw [h_expand] at h_sum_ge
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hq_sum, one_mul] at h_sum_ge
  dsimp [freeEnergy]
  linarith

end InfoGeometry.InformationGeometry.KMS

end noncomputable section
