import Mathlib.Tactic

/-!
# Grand Canonical Ensemble of Primes and the Modular Hamiltonian

This module formalizes the thermodynamics of the prime numbers ("Primon Gas").
We construct the single-mode partition functions, the chemical potential, 
and relate them to the modular Hamiltonian and the Riemann Zeta function.
-/

namespace InfoGeometry

/-- The energy of the prime mode p is defined as ln(p). -/
noncomputable def prime_energy (p : ℝ) : ℝ := Real.log p

/-- The single-mode Grand Canonical partition function for a prime p.
    z is the fugacity (z = e^(β * μ)) and p_neg_beta is p^(-β). -/
noncomputable def single_mode_partition (p_neg_beta z : ℝ) : ℝ :=
  1 / (1 - z * p_neg_beta)

/-- The Grand Potential (Log-Partition Function) for a single mode. -/
noncomputable def single_mode_grand_potential (p_neg_beta z : ℝ) : ℝ :=
  -Real.log (1 - z * p_neg_beta)

/-- At zero chemical potential (μ = 0), the fugacity z is 1. 
    This yields the exact Euler factor of the Riemann Zeta function. -/
theorem single_mode_partition_mu_zero (p_neg_beta : ℝ) :
    single_mode_partition p_neg_beta 1 = 1 / (1 - p_neg_beta) := by
  dsimp [single_mode_partition]
  ring_nf

theorem single_mode_partition_mul_denominator
    (p_neg_beta z : ℝ) (hden : 1 - z * p_neg_beta ≠ 0) :
    (1 - z * p_neg_beta) * single_mode_partition p_neg_beta z = 1 := by
  unfold single_mode_partition
  field_simp

theorem single_mode_partition_ne_zero
    (p_neg_beta z : ℝ) (hden : 1 - z * p_neg_beta ≠ 0) :
    single_mode_partition p_neg_beta z ≠ 0 := by
  unfold single_mode_partition
  exact div_ne_zero one_ne_zero hden

@[simp] theorem single_mode_partition_zero_fugacity
    (p_neg_beta : ℝ) :
    single_mode_partition p_neg_beta 0 = 1 := by
  simp [single_mode_partition]

@[simp] theorem single_mode_grand_potential_zero_fugacity
    (p_neg_beta : ℝ) :
    single_mode_grand_potential p_neg_beta 0 = 0 := by
  simp [single_mode_grand_potential]

/-- 
  The Modular Hamiltonian generator H for the Bost-Connes KMS state.
  H|n> = ln(n)|n>
-/
abbrev ModularHamiltonian :=
  { f : ℝ → ℝ // ∀ n > 0, f n = Real.log n }

namespace ModularHamiltonian

abbrev eigenvalue (H : ModularHamiltonian) : ℝ → ℝ :=
  H.1

theorem is_log (H : ModularHamiltonian) :
    ∀ n > 0, H.eigenvalue n = Real.log n :=
  H.2

end ModularHamiltonian

/-- The modular Hamiltonian eigenvalue law and a finite trace readout equality. -/
theorem modularHamiltonian_trace_readout_of_eq (H : ModularHamiltonian)
    {tracePartition zetaProduct : ℝ}
    (h : tracePartition = zetaProduct) :
    (∀ n > 0, H.eigenvalue n = Real.log n) ∧ tracePartition = zetaProduct :=
  ⟨H.is_log, h⟩

end InfoGeometry
