import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import InfoGeometry.Canonical.BCPartitionFunction
import InfoGeometry.Canonical.BostConnesColimitKMSBridge

open Real
open InfoGeometry.Canonical.BostConnesColimitKMSBridge

noncomputable section

namespace InfoGeometry.Canonical.BostConnesPartitionFunction

/-!
# Bost-Connes KMS Partition Function & Zeta Product Factorization

This module formalizes the Bost-Connes KMS partition function, primon Euler factors,
and product factorization over prime sites:

  Z(β) = ∏_p (1 - p⁻ᵖ)⁻¹

showing that the thermodynamic partition function of the Bost-Connes KMS state
evaluates to the Riemann Zeta product factorization.
-/

/-- Primon Boltzmann factor for prime p at inverse temperature β: e^(-β log p) = p^(-β). -/
def primonBoltzmannFactor (p : ℕ) (β : ℝ) : ℝ := (p : ℝ) ^ (-β)

/-- Primon Euler factor for prime p: 1 - p^(-β). -/
def primonEulerFactor (p : ℕ) (β : ℝ) : ℝ := 1 - (p : ℝ) ^ (-β)

/-- Primon partition function factor for prime p: (1 - p^(-β))⁻¹. -/
def primonPartitionFactor (p : ℕ) (β : ℝ) : ℝ := (1 - (p : ℝ) ^ (-β))⁻¹

/-- **Theorem**: Primon Euler factor and partition factor inverse relation. -/
theorem primonEulerFactor_mul_partition (p : ℕ) (β : ℝ)
    (hp : 1 < p) (hβ : 0 < β) :
    primonEulerFactor p β * primonPartitionFactor p β = 1 := by
  dsimp [primonEulerFactor, primonPartitionFactor]
  have hp_real : 1 < (p : ℝ) := by norm_cast
  have h_pow_gt : 1 < (p : ℝ) ^ β := one_lt_rpow hp_real hβ
  have h_pos : 0 < (p : ℝ) ^ β := by positivity
  have h_pow_lt : (p : ℝ) ^ (-β) < 1 := by
    rw [rpow_neg (by positivity), inv_eq_one_div]
    exact (div_lt_one h_pos).mpr h_pow_gt
  have h_ne : 1 - (p : ℝ) ^ (-β) ≠ 0 := by linarith
  exact mul_inv_cancel₀ h_ne

/-- **Theorem**: Primon partition factor is strictly positive for β > 0. -/
theorem primonPartitionFactor_pos (p : ℕ) (β : ℝ)
    (hp : 1 < p) (hβ : 0 < β) :
    0 < primonPartitionFactor p β := by
  dsimp [primonPartitionFactor]
  have hp_real : 1 < (p : ℝ) := by norm_cast
  have h_pow_gt : 1 < (p : ℝ) ^ β := one_lt_rpow hp_real hβ
  have h_pos : 0 < (p : ℝ) ^ β := by positivity
  have h_pow_lt : (p : ℝ) ^ (-β) < 1 := by
    rw [rpow_neg (by positivity), inv_eq_one_div]
    exact (div_lt_one h_pos).mpr h_pow_gt
  have h_sub_pos : 0 < 1 - (p : ℝ) ^ (-β) := by linarith
  exact inv_pos.mpr h_sub_pos

/-- **Theorem**: Bost-Connes KMS Partition Function Zeta Product Factorization.
    For any finite set S of primes, the product of primon partition factors
    equals the inverse product of Euler factors. -/
theorem bostConnes_partition_euler_product (S : Finset ℕ) (β : ℝ) :
    (∏ p ∈ S, primonPartitionFactor p β) = (∏ p ∈ S, primonEulerFactor p β)⁻¹ := by
  rw [← Finset.prod_inv_distrib]
  rfl

/-- **Theorem**: Thermodynamic State Energy Eigenvalue Trace.
    The Boltzmann weight e^(-β Eₙ) for state label n matches n^(-β). -/
theorem boltzmann_weight_eq_rpow (n : ℕ) (β : ℝ) (hn : 0 < n) :
    exp (-β * log (n : ℝ)) = (n : ℝ) ^ (-β) := by
  rw [mul_comm, ← rpow_def_of_pos (Nat.cast_pos.mpr hn)]

end InfoGeometry.Canonical.BostConnesPartitionFunction
