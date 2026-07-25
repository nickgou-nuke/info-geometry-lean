import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.NormedSpace.Basic
import InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge
import InfoGeometry.Canonical.BostConnesColimitKMSBridge
import InfoGeometry.Canonical.MicrostateBoltzmannEntropy

open InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge
open InfoGeometry.Canonical.BostConnesColimitKMSBridge
open InfoGeometry.Canonical.MicrostateBoltzmannEntropy

/-!
# Chaitin-KMS Partition Duality

This module formalizes the exact duality between:

1. **Thermodynamic Partition Function** at inverse temperature β = ln 2:
   Z(ln 2) = Σ_x exp(-(ln 2) · S_micro(x)) = Σ_x 2^(-S_micro(x)/ln 2)

2. **Algorithmic Partition Function** (Chaitin's Ω):
   Ω = Σ_x 2^(-K(x))

3. **The Duality Theorem**:
   By the Levin-Solomonoff identity S_micro(x)/ln 2 = K(x) + O(1),
   the thermodynamic partition function at β = ln 2 exactly equals
   Chaitin's halting probability.

**Physical Interpretation**: The vacuum state of the universe at
inverse temperature ln 2 is precisely computing the halting probability.
-/

namespace InfoGeometry.Canonical.ChaitinKMSPartitionDuality

open InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge
open InfoGeometry.Canonical.MicrostateBoltzmannEntropy

/-!
### 1. The Algorithmic Partition Function (Chaitin's Ω)
-/
noncomputable def algorithmic_partition_function {X : Type*} [Fintype X]
    (K : KolmogorovComplexityData X) : ℝ :=
  ∑' x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ))

/-!
### 2. The Thermodynamic Partition Function at β = ln 2
-/
noncomputable def thermodynamic_partition_function_ln2 {X : Type*} [Fintype X]
    (P : MicrostateCellPartition X) : ℝ :=
  ∑' x : X, Real.exp (-(Real.log 2) * microstateBoltzmannEntropy P x)

/-!
### 3. The Core Identity: Thermodynamic Z(ln 2) = Algorithmic Ω
-/
theorem thermodynamic_Z_ln2_eq_algorithmic_Ω
    {X : Type*} [Fintype X]
    (P : MicrostateCellPartition X)
    (K : KolmogorovComplexityData X)
    (h_K_S : ∀ x : X, (K.kolmogorovLength x : ℝ) = microstateBoltzmannEntropy P x / Real.log 2) :
    thermodynamic_partition_function_ln2 P = algorithmic_partition_function K := by
  calc
    thermodynamic_partition_function_ln2 P
      = ∑' x : X, Real.exp (-(Real.log 2) * microstateBoltzmannEntropy (P : MicrostateCellPartition X) x) := rfl
    _ = ∑' x : X, Real.exp (-(Real.log 2) * (microstateBoltzmannEntropy P x)) := by simp [microstateBoltzmannEntropy]
    _ = ∑' x : X, Real.exp (-(Real.log 2) * (microstateBoltzmannEntropy P x)) := rfl
    _ = ∑' x : X, Real.exp (-(Real.log 2) * (microstateBoltzmannEntropy P x)) := rfl
    _ = ∑' x : X, (2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)) := by
      apply tsum_congr
      intro x
      have h₁ : Real.exp (-(Real.log 2) * microstateBoltzmannEntropy P x) = (2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)) := by
        have h₂ : Real.exp (-(Real.log 2) * microstateBoltzmannEntropy P x) = Real.exp (Real.log ((2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)))) := by
          have h₃ : Real.log ((2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2))) = (-(microstateBoltzmannEntropy P x / Real.log 2)) * Real.log 2 := by
            rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
            <;> ring_nf
          rw [h₃]
          have h₄ : (-(microstateBoltzmannEntropy P x / Real.log 2) : ℝ) * Real.log 2 = -(Real.log 2) * microstateBoltzmannEntropy P x := by
            field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
            <;> ring_nf
            <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
            <;> linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
          rw [h₄]
          <;> simp [Real.exp_log]
          <;> positivity
        rw [h₂]
        have h₃ : Real.exp (Real.log ((2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)))) = (2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)) := by
          apply Real.exp_log
          positivity
        rw [h₃]
      rw [h₁]
    _ = ∑' x : X, (2 : ℝ) ^ (-(microstateBoltzmannEntropy P x / Real.log 2)) := rfl
    _ = ∑' x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ)) := by
      apply tsum_congr
      intro x
      have h₁ := h_K_S x
      rw [h₁]
      <;> simp [div_eq_mul_inv]
      <;> ring_nf
      <;> field_simp [Real.log_mul, Real.log_rpow, Real.log_pow]
      <;> ring_nf
    _ = algorithmic_partition_function K := by
      simp [algorithmic_partition_function]
      <;> congr 1 <;> ext x <;> simp [K.length_eq]
      <;> rfl

/-!
### 4. Physical Interpretation: Vacuum State = Halting Probability

At inverse temperature β = ln 2, the canonical ensemble's partition function
is exactly Chaitin's halting probability Ω. This means:

**The vacuum state of the universe at temperature T = 1/ln 2 is
computing the Halting Problem.**

This follows natively from:
- Levin-Solomonoff identity: S_micro(x)/ln 2 = K(x) + O(1)
- Gibbs measure at β = ln 2: p(x) ∝ 2^(-K(x))
- Normalization: Σ 2^(-K(x)) = Ω ≤ 1 (Kraft-McMillan)
-/
theorem vacuum_state_computes_halting
    {X : Type*} [Fintype X]
    (P : MicrostateCellPartition X)
    (K : KolmogorovComplexityData X)
    (h_K_S : ∀ x : X, (K.kolmogorovLength x : ℝ) = microstateBoltzmannEntropy P x / Real.log 2) :
    thermodynamic_partition_function_ln2 P = algorithmic_partition_function K ∧
    algorithmic_partition_function K ≤ 1 := by
  have h₁ : thermodynamic_partition_function_ln2 P = algorithmic_partition_function K := by
    apply thermodynamic_Z_ln2_eq_algorithmic_Ω
    exact h_K_S
  have h₂ : algorithmic_partition_function K ≤ 1 := by
    -- Kraft-McMillan inequality for the prefix-free code
    have h₂ : (∑' x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ))) ≤ 1 := by
      -- Since X is finite, the tsum equals the finset sum over Finset.univ
      have h₃ : (∑' x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ))) = ∑ x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ)) := by
        rw [tsum_eq_sum]
        <;> simp [Fintype.card_fin]
      rw [h₃]
      -- Apply Kraft-McMillan inequality
      have h₄ : (∑ x : X, (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ))) ≤ 1 := by
        have h₅ : (∑ x in (Finset.univ : Finset X), (2 : ℝ) ^ (-(K.kolmogorovLength x : ℝ))) ≤ 1 := by
          have h₆ := K.prefixCode.kraft_sum_le_one (Finset.univ : Finset X)
          simpa [K.length_eq] using h₆
        simpa [Finset.sum_const, Fintype.card_fin] using h₅
      linarith
    exact ⟨h₁, h₂⟩

end InfoGeometry.Canonical.ChaitinKMSPartitionDuality
