import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.PrimeIsingPartitionFunctionBridge

Finite Prime-Chain Ising Partition Function and Exact Factorization Bridge.

This module formalizes:
1. **Ising Spin Boolean Embeddings:**
   $\sigma \in \{ \text{false}, \text{true} \}^N \hookrightarrow \{-1, +1\}^N \subset \mathbb{R}^N$.
2. **Full and Pair Partition Functions:**
   $$Z_N(\lambda, \beta, w) = \sum_{\sigma \in \{\pm 1\}^N} e^{-\beta H(\sigma; w)}$$
   $$Z_N^{\mathrm{pair}}(\lambda, \beta, w) = \sum_{\sigma \in \{\pm 1\}^N} e^{-\beta H_{\mathrm{pair}}(\sigma; w)}$$
3. **Exact Factorization Theorem:**
   $$Z_N(\lambda, \beta, w) = \exp\left(\frac{\beta \lambda}{4} \sum_{i=1}^N \ell_i^2\right) \cdot Z_N^{\mathrm{pair}}(\lambda, \beta, w)$$
   proving that the self-energy diagonal deletion changes the partition function
   strictly by a strictly positive overall factor, preserving all Lee--Yang zeros in $w$.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimeIsingPartitionFunction

open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet.FinitePrimeChainData

variable {N : ℕ}

/-- Standard map from Bool spin to real spin ±1 -/
@[rep_depth thermo]
def toRealSpin (s : Bool) : ℝ :=
  if s then 1 else -1

/-- Configuration vector in ℝ^N from a boolean spin configuration -/
@[rep_depth thermo]
def isingSpinVal (σ : Fin N → Bool) (i : Fin N) : ℝ :=
  toRealSpin (σ i)

/-- 🏆 THEOREM 1: Every boolean configuration is genuine Ising: σᵢ² = 1 -/
@[rep_depth thermo]
theorem isingSpinVal_sq (σ : Fin N → Bool) (i : Fin N) :
    (isingSpinVal σ i) ^ 2 = 1 := by
  dsimp [isingSpinVal, toRealSpin]
  cases (σ i) <;> simp

/-- 🏆 THEOREM 2: The configuration satisfies IsIsingSpin predicate -/
@[rep_depth thermo]
theorem isingSpinVal_isIsingSpin (σ : Fin N → Bool) :
    IsIsingSpin (isingSpinVal σ) := by
  intro i
  exact isingSpinVal_sq σ i

/-- Full finite prime-chain Ising partition function Z_N(λ, β, w) -/
@[rep_depth thermo]
def primePartitionFunction (D : FinitePrimeChainData N) (lam beta w : ℝ) : ℝ :=
  ∑ σ : Fin N → Bool, Real.exp (- beta * D.spinHamiltonian lam w (isingSpinVal σ))

/-- Pair-interaction prime-chain partition function Z_N^pair(λ, β, w) without self-energy -/
@[rep_depth thermo]
def primePairPartitionFunction (D : FinitePrimeChainData N) (lam beta w : ℝ) : ℝ :=
  ∑ σ : Fin N → Bool, Real.exp (- beta * (
    - (1 / 2 : ℝ) * (∑ i, ∑ j, D.spinCoupling lam i j * isingSpinVal σ i * isingSpinVal σ j)
    + (w / 2) * (∑ i, D.ell i * isingSpinVal σ i)
  ))

/-- Constant self-energy factor e^{β λ / 4 ∑ᵢ ℓᵢ²} -/
@[rep_depth thermo]
def selfEnergyFactor (D : FinitePrimeChainData N) (lam beta : ℝ) : ℝ :=
  Real.exp (beta * (lam / 4) * ∑ i, (D.ell i)^2)

/-- 🏆 THEOREM 3: Exact Partition Function Factorization Theorem:
    $$Z_N(\lambda, \beta, w) = e^{\beta \lambda \sum_i \ell_i^2 / 4} Z_N^{\mathrm{pair}}(\lambda, \beta, w)$$ -/
@[rep_depth thermo]
theorem primePartitionFunction_eq_factor_mul_pair (D : FinitePrimeChainData N) (lam beta w : ℝ) :
    primePartitionFunction D lam beta w =
      selfEnergyFactor D lam beta * primePairPartitionFunction D lam beta w := by
  dsimp [primePartitionFunction, primePairPartitionFunction, selfEnergyFactor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have h_dec := D.spinHamiltonian_ising_decomposition lam w (isingSpinVal σ) (isingSpinVal_isIsingSpin σ)
  rw [h_dec]
  have h_exp_split :
    - beta * (- (1 / 2 : ℝ) * (∑ i, ∑ j, D.spinCoupling lam i j * isingSpinVal σ i * isingSpinVal σ j) +
              (w / 2) * (∑ i, D.ell i * isingSpinVal σ i) - (lam / 4) * ∑ i, (D.ell i)^2) =
    beta * (lam / 4) * (∑ i, (D.ell i)^2) +
    - beta * (- (1 / 2 : ℝ) * (∑ i, ∑ j, D.spinCoupling lam i j * isingSpinVal σ i * isingSpinVal σ j) +
              (w / 2) * (∑ i, D.ell i * isingSpinVal σ i)) := by ring
  rw [h_exp_split, Real.exp_add]

/-- 🏆 THEOREM 4: Positivity of the partition function -/
@[rep_depth thermo]
theorem primePartitionFunction_pos (D : FinitePrimeChainData N) [Nonempty (Fin N → Bool)] (lam beta w : ℝ) :
    0 < primePartitionFunction D lam beta w := by
  dsimp [primePartitionFunction]
  apply Finset.sum_pos
  · intro σ _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

end InfoGeometry.Canonical.PrimeIsingPartitionFunction
