import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Araki–Donald Variational Principle for Quantum Relative Entropy

This module formalizes:
1. The Donald perturbation functional:
     Ψ_{p, q}(h) = ∑_i p_i * h_i - log(∑_i q_i * exp(h_i))
2. THEOREM 1 (Donald Variational Upper Bound):
     For any perturbation Hamiltonian h:
       ∑_i p_i * h_i - log(∑_i q_i * exp(h_i)) ≤ D_KL(p ∥ q)
3. THEOREM 2 (Exact Supremum Attainment at Modular Logarithm):
     For the relative modular generator h*_i = log(p_i / q_i):
       Ψ_{p, q}(h*) = D_KL(p ∥ q)
4. MASTER THEOREM 3 (Araki–Donald Variational Representation):
     D_KL(p ∥ q) = max_h ( ∑_i p_i * h_i - log(∑_i q_i * exp(h_i)) )
5. THEOREM 4 (Non-Negativity / Klein Inequality as Corollaries):
     Setting h = 0 yields D_KL(p ∥ q) ≥ 0.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.InformationGeometry.ArakiDonald

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
=============================================================================
PART 1: The Donald Perturbation Functional
=============================================================================
-/

/-- The relative entropy / Kullback–Leibler / Umegaki divergence: D_KL(p ∥ q). -/
def relativeEntropy (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * Real.log (p i / q i)

/-- The perturbed partition functional: Z_q(h) = ∑_i q_i * exp(h_i). -/
def perturbedPartition (q : ι → ℝ) (h : ι → ℝ) : ℝ :=
  ∑ i, q i * Real.exp (h i)

/-- The Donald perturbation functional: Ψ_{p, q}(h) = ∑_i p_i * h_i - log(Z_q(h)). -/
def donaldFunctional (p q : ι → ℝ) (h : ι → ℝ) : ℝ :=
  (∑ i, p i * h i) - Real.log (perturbedPartition q h)

/-!
=============================================================================
PART 2: Variational Bounds and Attainment
=============================================================================
-/

lemma log_bound (x : ℝ) (hx : 0 < x) :
    1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-- 
  MASTER THEOREM 1 (Donald Variational Upper Bound):
  For ANY perturbation vector h and normalized probability states p, q:
    Ψ_{p, q}(h) ≤ D_KL(p ∥ q)
-/
theorem donald_variational_upper_bound [Nonempty ι]
    (p q : ι → ℝ) (h : ι → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1)
    (hq_sum : ∑ i, q i = 1) :
    donaldFunctional p q h ≤ relativeEntropy p q := by
  dsimp [donaldFunctional, relativeEntropy, perturbedPartition]
  -- Let Z = perturbedPartition q h > 0
  have hZ_pos : 0 < ∑ i, q i * Real.exp (h i) := by
    exact sum_pos (fun i _ => mul_pos (hq_pos i) (Real.exp_pos (h i))) univ_nonempty

  -- Define the perturbed state q_h(i) = q(i) * exp(h(i)) / Z
  let q_h := fun i => (q i * Real.exp (h i)) / (∑ j, q j * Real.exp (h j))
  have hq_h_pos (i : ι) : 0 < q_h i := div_pos (mul_pos (hq_pos i) (Real.exp_pos (h i))) hZ_pos
  have hq_h_sum : ∑ i, q_h i = 1 := by
    dsimp [q_h]
    rw [← sum_div, div_self (ne_of_gt hZ_pos)]

  -- Klein's inequality: D_KL(p ∥ q_h) ≥ 0
  have h_term_ge (i : ι) :
      p i * (1 - q_h i / p i) ≤ p i * Real.log (p i / q_h i) := by
    have h_ratio : 0 < p i / q_h i := div_pos (hp_pos i) (hq_h_pos i)
    have h_log := log_bound (p i / q_h i) h_ratio
    have h_inv : (p i / q_h i)⁻¹ = q_h i / p i := inv_div (p i) (q_h i)
    rw [h_inv] at h_log
    nlinarith [le_of_lt (hp_pos i)]
  
  have h_sum_ge : 0 ≤ ∑ i, p i * Real.log (p i / q_h i) := by
    have h_lhs : ∑ i, p i * (1 - q_h i / p i) = 0 := by
      calc
        ∑ i, p i * (1 - q_h i / p i) = ∑ i, (p i - p i * (q_h i / p i)) := by
          apply sum_congr rfl; intro i _; ring
        _ = ∑ i, (p i - q_h i) := by
          apply sum_congr rfl; intro i _
          rw [mul_div_cancel₀ (q_h i) (ne_of_gt (hp_pos i))]
        _ = (∑ i, p i) - (∑ i, q_h i) := by rw [sum_sub_distrib]
        _ = 1 - 1 := by rw [hp_sum, hq_h_sum]
        _ = 0 := sub_self 1
    calc
      0 = ∑ i, p i * (1 - q_h i / p i) := h_lhs.symm
      _ ≤ ∑ i, p i * Real.log (p i / q_h i) := sum_le_sum (fun i _ => h_term_ge i)

  -- Expand log(p / q_h) = log(p / q) - h + log(Z)
  have h_expand (i : ι) :
      p i * Real.log (p i / q_h i) =
        p i * Real.log (p i / q i) - p i * h i + p i * Real.log (∑ j, q j * Real.exp (h j)) := by
    dsimp [q_h]
    rw [Real.log_div (ne_of_gt (hp_pos i)) (ne_of_gt (hq_h_pos i))]
    rw [Real.log_div (ne_of_gt (mul_pos (hq_pos i) (Real.exp_pos (h i)))) (ne_of_gt hZ_pos)]
    rw [Real.log_mul (ne_of_gt (hq_pos i)) (ne_of_gt (Real.exp_pos (h i)))]
    rw [Real.log_exp]
    rw [Real.log_div (ne_of_gt (hp_pos i)) (ne_of_gt (hq_pos i))]
    ring

  simp_rw [h_expand] at h_sum_ge
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hp_sum, one_mul] at h_sum_ge
  linarith

/-- The relative modular generator: h*_i = log(p_i / q_i). -/
def relativeModularGenerator (p q : ι → ℝ) (i : ι) : ℝ :=
  Real.log (p i / q i)

/-- 
  MASTER THEOREM 2 (Exact Supremum Attainment at Modular Logarithm):
  When h = h* = log(p / q), the Donald functional attains the relative entropy exactly:
    Ψ_{p, q}(h*) = D_KL(p ∥ q)
-/
theorem donald_variational_exact_attainment [Nonempty ι]
    (p q : ι → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1) :
    donaldFunctional p q (relativeModularGenerator p q) = relativeEntropy p q := by
  dsimp [donaldFunctional, relativeEntropy, perturbedPartition, relativeModularGenerator]
  have h_exp (i : ι) : Real.exp (Real.log (p i / q i)) = p i / q i :=
    Real.exp_log (div_pos (hp_pos i) (hq_pos i))
  simp_rw [h_exp]
  have h_cancel (i : ι) : q i * (p i / q i) = p i := by
    rw [mul_div_cancel₀ (p i) (ne_of_gt (hq_pos i))]
  simp_rw [h_cancel]
  rw [hp_sum, Real.log_one, sub_zero]

/-- 
  MASTER THEOREM 3 (Araki–Donald Variational Characterization):
  D_KL(p ∥ q) is the exact supremum of the Donald functional over all perturbations h:
    D_KL(p ∥ q) = max_h Ψ_{p, q}(h)
-/
theorem araki_donald_variational_principle [Nonempty ι]
    (p q : ι → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1)
    (hq_sum : ∑ i, q i = 1) :
    (∀ h, donaldFunctional p q h ≤ relativeEntropy p q) ∧
    (∃ h, donaldFunctional p q h = relativeEntropy p q) := by
  constructor
  · intro h
    exact donald_variational_upper_bound p q h hp_pos hq_pos hp_sum hq_sum
  · use (relativeModularGenerator p q)
    exact donald_variational_exact_attainment p q hp_pos hq_pos hp_sum

/-- 
  COROLLARY (Klein's Inequality from Zero Perturbation):
  Evaluating the Donald functional at h = 0 proves D_KL(p ∥ q) ≥ 0 natively.
-/
theorem relative_entropy_nonneg_of_donald [Nonempty ι]
    (p q : ι → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hq_pos : ∀ i, 0 < q i)
    (hp_sum : ∑ i, p i = 1)
    (hq_sum : ∑ i, q i = 1) :
    0 ≤ relativeEntropy p q := by
  have h_bound := donald_variational_upper_bound p q (fun _ => 0) hp_pos hq_pos hp_sum hq_sum
  dsimp [donaldFunctional, perturbedPartition] at h_bound
  simp_rw [Real.exp_zero, mul_one, mul_zero, sum_const_zero, hq_sum, Real.log_one, sub_zero] at h_bound
  exact h_bound

end InfoGeometry.InformationGeometry.ArakiDonald

end noncomputable section
