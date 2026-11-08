import InfoGeometry.Arithmetic.ChiralPrimonGasVarianceBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimonFockTraceFinite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrixBridge

2x2 Covariance / Fisher Information Matrix Positive Semidefiniteness for the
Chiral Primon Gas.

This module formalizes:
1. **Strict Positivity of Prime Energy:**
   $$p \text{ prime} \implies p \ge 2 \implies E_p = \ln p > 0$$
2. **Local Rank-One Quadratic Factorization:**
   $$a^2 \operatorname{Var}_p(E) + 2ab \operatorname{Cov}_p(E, N) + b^2 \operatorname{Var}_p(N) = v_p (a E_p + b)^2 \ge 0$$
3. **Sector Covariance Matrix Positive Semidefiniteness (PSD):**
   $$\Sigma_G = \sum_{p \in G} v_p \begin{pmatrix} E_p \\ 1 \end{pmatrix} \begin{pmatrix} E_p & 1 \end{pmatrix} \succeq 0$$
   $$\forall a, b \in \mathbb{R}, \quad a^2 \operatorname{Var}(E) + 2ab \operatorname{Cov}(E, N) + b^2 \operatorname{Var}(N) \ge 0$$
4. **Universal Fermionic Local Variance Bound:**
   $$0 \le v_p = n_p(1 - n_p) \le \frac{1}{4}$$
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrix

open InfoGeometry.Arithmetic.ChiralPrimonGas
open InfoGeometry.Arithmetic.ChiralPrimonGasVarianceBridge

/-! The occupation formula is written branchwise for numerical stability, but
it is exactly the usual two-state Fock/Gibbs occupation. -/

theorem occupation_fermion_eq_modeWeight_div_one_add
    (beta nu : ℝ) (p : ℕ) :
    occupation Statistics.fermion beta nu p =
      modeWeight beta nu p / (1 + modeWeight beta nu p) := by
  unfold occupation
  by_cases hx : 0 ≤ beta * primeEnergy p - nu
  · simp [hx, modeWeight]
  · simp only [hx, ↓reduceIte, modeWeight]
    let x : ℝ := beta * primeEnergy p - nu
    have harg : nu - beta * primeEnergy p = -x := by
      dsimp [x]
      ring
    rw [harg, Real.exp_neg]
    have hexp : Real.exp x ≠ 0 := Real.exp_ne_zero x
    field_simp
    ring

/-! The same logistic weight is the local factor of the native finite Fock
trace after the usual chemical-potential energy shift. -/

theorem fockTraceExp_prime_shift_eq_modeWeight_prod
    {n : ℕ} (p : Fin n → ℕ) (beta nu : ℝ) (hbeta : beta ≠ 0) :
    InfoGeometry.Arithmetic.PrimonFockTraceFinite.fockTraceExp n
        (fun i => primeEnergy (p i) - nu / beta) beta =
      ∏ i : Fin n, (1 + modeWeight beta nu (p i)) := by
  rw [InfoGeometry.Arithmetic.PrimonFockTraceFinite.fockTraceExp_eq_product]
  apply Finset.prod_congr rfl
  intro i _hi
  unfold InfoGeometry.Arithmetic.PrimonFockTraceFinite.localBoltzmann modeWeight
  congr 1
  field_simp
  ring

/-- 🏆 THEOREM 1: Strict Positivity of Prime Energy for Primes (p ≥ 2) -/
theorem primeEnergy_pos_of_prime {p : ℕ} (hp : Nat.Prime p) :
    0 < primeEnergy p := by
  unfold primeEnergy
  apply Real.log_pos
  have h2 : 2 ≤ p := hp.two_le
  exact_mod_cast h2

/-- 🏆 THEOREM 2: Local Quadratic Form Factorization:
    $$a^2 \operatorname{Var}_p(E) + 2ab \operatorname{Cov}_p(E,N) + b^2 \operatorname{Var}_p(N) = v_p (a E_p + b)^2$$ -/
theorem local_quadratic_factorization (beta nu a b : ℝ) (p : ℕ) :
    a^2 * localEnergyVariance Statistics.fermion beta nu p +
    2 * a * b * localEnergyNumberCovariance Statistics.fermion beta nu p +
    b^2 * localNumberVariance Statistics.fermion beta nu p =
    localNumberVariance Statistics.fermion beta nu p * (a * primeEnergy p + b)^2 := by
  unfold localEnergyVariance localEnergyNumberCovariance
  ring

/-- 🏆 THEOREM 3: Local Quadratic Nonnegativity -/
theorem local_quadratic_nonneg (beta nu a b : ℝ) (p : ℕ) :
    0 ≤ a^2 * localEnergyVariance Statistics.fermion beta nu p +
        2 * a * b * localEnergyNumberCovariance Statistics.fermion beta nu p +
        b^2 * localNumberVariance Statistics.fermion beta nu p := by
  rw [local_quadratic_factorization]
  exact mul_nonneg (localNumberVariance_fermion_nonneg beta nu p) (sq_nonneg _)

/-- 🏆 THEOREM 4: Sector Covariance Matrix Positive Semidefiniteness (PSD):
    $$\forall a, b \in \mathbb{R}, \quad a^2 \operatorname{Var}(E) + 2ab \operatorname{Cov}(E, N) + b^2 \operatorname{Var}(N) \ge 0$$ -/
theorem sector_covariance_quadratic_nonneg_of_fermion
    (G : PrimonGas) (hG : G.statistics = Statistics.fermion)
    (beta nu a b : ℝ) :
    0 ≤ a^2 * (sector G beta nu).varEnergy +
        2 * a * b * (sector G beta nu).covEnergyNumber +
        b^2 * (sector G beta nu).varNumber := by
  simp only [sector, hG]
  have h_sum :
      a^2 * (∑ p ∈ G.register.primes, localEnergyVariance Statistics.fermion beta nu p) +
      2 * a * b * (∑ p ∈ G.register.primes, localEnergyNumberCovariance Statistics.fermion beta nu p) +
      b^2 * (∑ p ∈ G.register.primes, localNumberVariance Statistics.fermion beta nu p) =
      ∑ p ∈ G.register.primes,
        (a^2 * localEnergyVariance Statistics.fermion beta nu p +
         2 * a * b * localEnergyNumberCovariance Statistics.fermion beta nu p +
         b^2 * localNumberVariance Statistics.fermion beta nu p) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [h_sum]
  exact Finset.sum_nonneg (fun p _ => local_quadratic_nonneg beta nu a b p)

/-- 🏆 THEOREM 5: Universal Fermionic Local Variance Upper Bound ($v_p \le 1/4$) -/
theorem localNumberVariance_fermion_le_quarter (beta nu : ℝ) (p : ℕ) :
    localNumberVariance Statistics.fermion beta nu p ≤ 1 / 4 := by
  dsimp [localNumberVariance]
  have h_alg (x : ℝ) : x * (1 - x) = 1 / 4 - (x - 1 / 2)^2 := by ring
  rw [h_alg]
  have : 0 ≤ (occupation Statistics.fermion beta nu p - 1 / 2)^2 := sq_nonneg _
  linarith

end InfoGeometry.Arithmetic.ChiralPrimonGasFisherMatrix
