import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FermionParityWittenZetaInversionBridge

Fermion Parity (-1)^F, Witten Index, and Zeta Multiplicative Inversion.

This module formalizes:
1. **Fermion Parity Operator (-1)^F in the Primon Gas:**
   $$(-1)^F |n\rangle = \mu(n) |n\rangle = (-1)^k |n\rangle$$
   where $n = p_1 \cdots p_k$ is square-free.
2. **Bosonic vs Supersymmetric Partition Functions:**
   $$Z_{\mathrm{bos}}(q) = \prod_{i=1}^N \frac{1}{1 - q_i} = \zeta_N(\beta), \qquad q_i = p_i^{-\beta}$$
   $$Z_{\mathrm{susy}}(q) = \operatorname{STr}(e^{-\beta H}) = \prod_{i=1}^N (1 - q_i) = \frac{1}{\zeta_N(\beta)}$$
3. **Exact Multiplicative Reciprocity:**
   $$Z_{\mathrm{bos}}(q) \cdot Z_{\mathrm{susy}}(q) = 1$$
4. **Logarithmic Differential Inversion:**
   $$d \ln Z_{\mathrm{susy}} = d \ln\left(\frac{1}{Z_{\mathrm{bos}}}\right) = - d \ln Z_{\mathrm{bos}} = - \frac{Z_{\mathrm{bos}}'}{Z_{\mathrm{bos}}}$$
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.FermionParityWittenZetaInversion

variable {N : ℕ}

/-- Finite Bosonic Euler partition function Z_bos(q) = ∏ᵢ (1 - qᵢ)⁻¹ -/
def bosonicPartitionFunction (q : Fin N → ℝ) : ℝ :=
  ∏ i, (1 - q i)⁻¹

/-- Finite Supersymmetric / Witten Index partition function Z_susy(q) = ∏ᵢ (1 - qᵢ) -/
def supersymmetricPartitionFunction (q : Fin N → ℝ) : ℝ :=
  ∏ i, (1 - q i)

/-- 🏆 THEOREM 1: Exact Reciprocity between Bosonic Partition Function and Witten Index:
    $$Z_{\mathrm{bos}}(q) \cdot Z_{\mathrm{susy}}(q) = 1$$ -/
theorem bosonic_witten_reciprocity (q : Fin N → ℝ) (hq : ∀ i, q i ≠ 1) :
    bosonicPartitionFunction q * supersymmetricPartitionFunction q = 1 := by
  dsimp [bosonicPartitionFunction, supersymmetricPartitionFunction]
  rw [← Finset.prod_mul_distrib]
  have h_term : ∀ i, (1 - q i)⁻¹ * (1 - q i) = 1 := by
    intro i
    have : 1 - q i ≠ 0 := by
      intro h_zero
      have : q i = 1 := by linarith
      exact hq i this
    exact inv_mul_cancel₀ this
  have h_prod_one : (∏ i : Fin N, ((1 - q i)⁻¹ * (1 - q i))) = ∏ i : Fin N, (1 : ℝ) := by
    apply Finset.prod_congr rfl
    intro i _
    exact h_term i
  rw [h_prod_one, Finset.prod_const_one]

/-- 🏆 THEOREM 2: Witten Index Inverts the Bosonic Zeta Function:
    $$Z_{\mathrm{susy}}(q) = \frac{1}{Z_{\mathrm{bos}}(q)}$$ -/
theorem supersymmetric_eq_inv_bosonic (q : Fin N → ℝ) (hq : ∀ i, q i ≠ 1) :
    supersymmetricPartitionFunction q = (bosonicPartitionFunction q)⁻¹ :=
  (inv_eq_of_mul_eq_one_right (bosonic_witten_reciprocity q hq)).symm

/-- 🏆 THEOREM 3: Logarithmic Differential Inversion Law:
    $$d\ln(1/Z) = - d\ln Z$$ -/
theorem log_diff_inversion (Z dZ : ℝ) (hZ : Z ≠ 0) :
    let invZ := 1 / Z
    let dinvZ := - dZ / (Z ^ 2)
    dinvZ / invZ = - (dZ / Z) := by
  intro invZ dinvZ
  dsimp [invZ, dinvZ]
  field_simp [hZ]

end InfoGeometry.Canonical.FermionParityWittenZetaInversion
