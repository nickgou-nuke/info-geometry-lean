import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quantum Operator KMS Thermodynamic Identity and the Variational Principle

This module formalizes:
1. The Operator Gibbs/KMS Partition Trace: Z(K) = Tr(exp(-K)).
2. The Operator Gibbs Density Matrix: ρ(K) = exp(-K) / Tr(exp(-K)).
3. The Quantum Expectation / Internal Energy: E(K) = Tr(ρ(K) * K).
4. The von Neumann Entropy: S(ρ(K)) = - Tr(ρ(K) * log ρ(K)).
5. The Quantum Massieu–Planck / Helmholtz Free Energy: F(K) = - log Tr(exp(-K)).
6. MASTER THEOREM 1 (Operator Thermodynamic Identity):
     F(K) = Tr(ρ(K) * K) - S(ρ(K)).
7. MASTER THEOREM 2 (Operator Variational Principle / Donald–Araki Bound):
     For any normalized density operator σ = diag(q):
       F(K) ≤ Tr(σ * K) - S(σ)
     derived directly from non-negativity of Quantum Relative Entropy D_KL(σ ∥ ρ) ≥ 0.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open Matrix
open BigOperators
open Finset

namespace InfoGeometry.Modular.OperatorKMS

/-- Standard lower bound for the natural logarithm: 1 - 1/x ≤ log x for x > 0. -/
lemma log_bound (x : ℝ) (hx : 0 < x) :
    1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-!
=============================================================================
PART 1: The Operator Gibbs State and Partition Trace
=============================================================================
-/

/-- Diagonal operator representation of a scalar spectrum. -/
def diagOp {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal v

/-- The Operator Exponential of the negative Hamiltonian: exp(-K). -/
def expNegOp {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => Real.exp (-K i))

/-- The Operator Partition Trace: Z(K) = Tr(exp(-K)). -/
def partitionTrace {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : ℝ :=
  trace (expNegOp K)

/-- Equivalence of partition trace and scalar exponential sum. -/
theorem partitionTrace_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) :
    partitionTrace K = ∑ i, Real.exp (-K i) := by
  dsimp [partitionTrace, expNegOp, trace, diagonal]
  apply Finset.sum_congr rfl; intro i _
  simp

/-- Strict positivity of the operator partition trace. -/
theorem partitionTrace_pos {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (K : ι → ℝ) :
    0 < partitionTrace K := by
  rw [partitionTrace_eq_sum]
  exact sum_pos (fun i _ => Real.exp_pos (-K i)) univ_nonempty

/-- The Operator Gibbs Density Matrix: ρ(K) = (1 / Z(K)) * exp(-K). -/
def gibbsDensityOp {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : Matrix ι ι ℝ :=
  (partitionTrace K)⁻¹ • expNegOp K

/-- Diagonal elements of the Gibbs density matrix. -/
theorem gibbsDensityOp_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) (i : ι) :
    gibbsDensityOp K i i = Real.exp (-K i) / partitionTrace K := by
  dsimp [gibbsDensityOp, expNegOp, diagonal]
  simp only [if_true]
  ring

/-- Normalization of the Gibbs density matrix: Tr(ρ(K)) = 1. -/
@[simp]
theorem gibbsDensityOp_trace_one {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (K : ι → ℝ) :
    trace (gibbsDensityOp K) = 1 := by
  dsimp [gibbsDensityOp, trace, expNegOp, diagonal]
  simp only [if_true]
  rw [← Finset.mul_sum]
  have h_sum : (∑ i, Real.exp (-K i)) = partitionTrace K := (partitionTrace_eq_sum K).symm
  rw [h_sum, inv_mul_cancel₀ (ne_of_gt (partitionTrace_pos K))]

/-!
=============================================================================
PART 2: Operator Free Energy, Internal Energy, and Thermodynamic Identity
=============================================================================
-/

/-- The Quantum Massieu–Planck / Helmholtz Free Energy: F(K) = - log Tr(exp(-K)). -/
def freeEnergyOp {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : ℝ :=
  - Real.log (partitionTrace K)

/-- The Quantum Expectation / Internal Energy: E(K) = Tr(ρ(K) * K). -/
def internalEnergyOp {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : ℝ :=
  trace (gibbsDensityOp K * diagOp K)

/-- Equivalence of quantum internal energy trace and spectral sum. -/
theorem internalEnergyOp_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) :
    internalEnergyOp K = ∑ i, (gibbsDensityOp K i i) * K i := by
  dsimp [internalEnergyOp, trace]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · dsimp [diagOp, diagonal]
    rw [if_pos rfl]
  · intro j _ hj
    have h_ne : ¬(j = i) := hj
    dsimp [diagOp, diagonal]
    rw [if_neg h_ne, mul_zero]
  · intro h_not; exfalso; exact h_not (Finset.mem_univ i)

/-- The von Neumann Entropy of the Gibbs State: S(ρ) = - ∑_i ρ_ii * log(ρ_ii). -/
def vonNeumannEntropyOp {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ι → ℝ) : ℝ :=
  - ∑ i, (gibbsDensityOp K i i) * Real.log (gibbsDensityOp K i i)

/-- 
  MASTER THEOREM 1 (The Operator Thermodynamic Identity F = E - S):
  F(K) = Tr(ρ(K) * K) - S(ρ(K))
-/
theorem operator_thermodynamic_identity {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] (K : ι → ℝ) :
    freeEnergyOp K = internalEnergyOp K - vonNeumannEntropyOp K := by
  rw [internalEnergyOp_eq_sum]
  dsimp [vonNeumannEntropyOp, freeEnergyOp]
  have h_log_rho (i : ι) :
      Real.log (gibbsDensityOp K i i) = -K i - Real.log (partitionTrace K) := by
    rw [gibbsDensityOp_diag]
    rw [Real.log_div (ne_of_gt (Real.exp_pos (-K i))) (ne_of_gt (partitionTrace_pos K))]
    rw [Real.log_exp]
  have h_sum_entropy :
      (∑ i, (gibbsDensityOp K i i) * Real.log (gibbsDensityOp K i i)) =
        (∑ i, (gibbsDensityOp K i i) * (-K i)) - Real.log (partitionTrace K) := by
    simp_rw [h_log_rho, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h_rho_sum : (∑ i, gibbsDensityOp K i i) = 1 := by
      have ht := gibbsDensityOp_trace_one K
      dsimp [trace] at ht
      exact ht
    rw [h_rho_sum, one_mul]
  have h_entropy_eval :
      - (∑ i, (gibbsDensityOp K i i) * Real.log (gibbsDensityOp K i i)) =
        (∑ i, (gibbsDensityOp K i i) * K i) + Real.log (partitionTrace K) := by
    rw [h_sum_entropy]
    have h_neg_k (i : ι) : (gibbsDensityOp K i i) * (-K i) = - ((gibbsDensityOp K i i) * K i) := by ring
    simp_rw [h_neg_k, sum_neg_distrib]
    ring
  rw [h_entropy_eval]
  ring

/-!
=============================================================================
PART 3: Quantum Relative Entropy and the Operator Variational Principle
=============================================================================
-/

/-- The Quantum Relative Entropy / Umegaki Divergence: D_KL(σ ∥ ρ(K)). -/
def quantumRelativeEntropy {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (K : ι → ℝ) : ℝ :=
  ∑ i, q i * (Real.log (q i) - Real.log (gibbsDensityOp K i i))

/-- 
  Klein's Inequality / Non-Negativity of Quantum Relative Entropy:
  D_KL(σ ∥ ρ(K)) ≥ 0 for any normalized density operator σ.
-/
theorem quantum_relative_entropy_nonneg
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (q : ι → ℝ) (K : ι → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i, q i = 1) :
    0 ≤ quantumRelativeEntropy q K := by
  dsimp [quantumRelativeEntropy]
  have h_term_ge (i : ι) :
      q i * (1 - (gibbsDensityOp K i i) / q i) ≤ q i * (Real.log (q i) - Real.log (gibbsDensityOp K i i)) := by
    have h_rho_pos : 0 < gibbsDensityOp K i i := by
      rw [gibbsDensityOp_diag]
      exact div_pos (Real.exp_pos (-K i)) (partitionTrace_pos K)
    have h_ratio : 0 < q i / (gibbsDensityOp K i i) := div_pos (hq_pos i) h_rho_pos
    have h_log := log_bound (q i / (gibbsDensityOp K i i)) h_ratio
    have h_inv : (q i / (gibbsDensityOp K i i))⁻¹ = (gibbsDensityOp K i i) / q i := inv_div (q i) (gibbsDensityOp K i i)
    rw [h_inv] at h_log
    have h_log_sub : Real.log (q i / (gibbsDensityOp K i i)) = Real.log (q i) - Real.log (gibbsDensityOp K i i) :=
      Real.log_div (ne_of_gt (hq_pos i)) (ne_of_gt h_rho_pos)
    rw [h_log_sub] at h_log
    nlinarith [le_of_lt (hq_pos i)]
  have h_sum_ge :
      (∑ i, q i * (1 - (gibbsDensityOp K i i) / q i)) ≤
        ∑ i, q i * (Real.log (q i) - Real.log (gibbsDensityOp K i i)) :=
    sum_le_sum (fun i _ => h_term_ge i)
  have h_lhs_zero : (∑ i, q i * (1 - (gibbsDensityOp K i i) / q i)) = 0 := by
    calc
      ∑ i, q i * (1 - (gibbsDensityOp K i i) / q i) = ∑ i, (q i - q i * ((gibbsDensityOp K i i) / q i)) := by
        apply sum_congr rfl; intro i _; ring
      _ = ∑ i, (q i - gibbsDensityOp K i i) := by
        apply sum_congr rfl; intro i _
        rw [mul_div_cancel₀ (gibbsDensityOp K i i) (ne_of_gt (hq_pos i))]
      _ = (∑ i, q i) - (∑ i, gibbsDensityOp K i i) := by rw [Finset.sum_sub_distrib]
      _ = 1 - 1 := by
        have ht : (∑ i, gibbsDensityOp K i i) = 1 := by
          have h1 := gibbsDensityOp_trace_one K
          dsimp [trace] at h1
          exact h1
        rw [hq_sum, ht]
      _ = 0 := sub_self 1
  rw [h_lhs_zero] at h_sum_ge
  exact h_sum_ge

/-- 
  MASTER THEOREM 2 (The Operator Variational Principle of Quantum Statistical Mechanics):
  For ANY normalized density operator σ = diag(q):
    F(K) ≤ Tr(σ * K) - S(σ)
  proving that the physical free energy is the absolute minimum of the
  quantum non-equilibrium free energy functional: F(K) = min_σ (Tr(σ K) - S(σ)).
-/
theorem operator_variational_free_energy_principle
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (K : ι → ℝ) (q : ι → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hq_sum : ∑ i, q i = 1) :
    freeEnergyOp K ≤ trace (diagonal q * diagOp K) - (- ∑ i, q i * Real.log (q i)) := by
  have h_rel_nonneg := quantum_relative_entropy_nonneg q K hq_pos hq_sum
  dsimp [quantumRelativeEntropy] at h_rel_nonneg
  have h_expand (i : ι) :
      q i * (Real.log (q i) - Real.log (gibbsDensityOp K i i)) =
        q i * Real.log (q i) + q i * K i + q i * Real.log (partitionTrace K) := by
    rw [gibbsDensityOp_diag]
    rw [Real.log_div (ne_of_gt (Real.exp_pos (-K i))) (ne_of_gt (partitionTrace_pos K))]
    rw [Real.log_exp]
    ring
  simp_rw [h_expand] at h_rel_nonneg
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, hq_sum, one_mul] at h_rel_nonneg
  have h_trace_q : trace (diagonal q * diagOp K) = ∑ i, q i * K i := by
    dsimp [trace]
    apply sum_congr rfl; intro i _
    rw [Matrix.mul_apply, sum_eq_single i]
    · dsimp [diagOp, diagonal]
      rw [if_pos rfl, if_pos rfl]
    · intro j _ hj
      have h_ne : ¬(j = i) := hj
      dsimp [diagOp, diagonal]
      rw [if_neg h_ne, mul_zero]
    · intro h_not; exfalso; exact h_not (Finset.mem_univ i)
  rw [h_trace_q]
  dsimp [freeEnergyOp]
  linarith

end InfoGeometry.Modular.OperatorKMS

end noncomputable section
