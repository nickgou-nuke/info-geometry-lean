import InfoGeometry.Canonical.PrimePartitionPolynomials

/-!
# Finite positivity of the coarse prime-chain partition polynomial

The polynomial owner supplies the finite partition polynomial and keeps the
Lee--Yang circle law as a witness.  This file proves an unconditional finite
fact: its constant coefficient is positive, hence the polynomial is nonzero.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Canonical.PrimePartitionPolynomialFinitePositivityBridge

open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimePartitionPolynomials

variable {N : ℕ}

theorem occupiedCount_le (σ : SpinConfig N) :
    occupiedCount σ ≤ N := by
  calc
    occupiedCount σ = ∑ i : Fin N, if σ i then 1 else 0 := rfl
    _ ≤ ∑ _i : Fin N, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      split <;> omega
    _ = N := by simp

theorem partitionPolynomial_coeff_zero_eq_real_sum
    (D : FinitePrimeChainData N) (lam : ℝ) :
    (partitionPolynomial D lam).coeff 0 =
      ((∑ σ : SpinConfig N,
        if occupiedCount σ = 0 then configurationWeight D lam σ else 0 : ℝ) : ℂ) := by
  calc
    (partitionPolynomial D lam).coeff 0 =
        ∑ σ : SpinConfig N,
          if occupiedCount σ = 0 then (configurationWeight D lam σ : ℂ) else 0 := by
      simp [partitionPolynomial, Polynomial.coeff_mul, eq_comm]
    _ = ∑ σ : SpinConfig N,
          ((if occupiedCount σ = 0 then configurationWeight D lam σ else 0 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases h : occupiedCount σ = 0 <;> simp [h]
    _ = ((∑ σ : SpinConfig N,
        if occupiedCount σ = 0 then configurationWeight D lam σ else 0 : ℝ) : ℂ) := by
      norm_cast

theorem partitionPolynomial_coeff_zero_pos
    (D : FinitePrimeChainData N) (lam : ℝ) :
    0 < ∑ σ : SpinConfig N,
      if occupiedCount σ = 0 then configurationWeight D lam σ else 0 := by
  apply Finset.sum_pos'
  · intro σ hσ
    by_cases h : occupiedCount σ = 0
    · simp [h, le_of_lt (configurationWeight_pos D lam σ)]
    · simp [h]
  · refine ⟨(fun _ : Fin N => false), Finset.mem_univ _, ?_⟩
    simp [occupiedCount, configurationWeight_pos]

theorem partitionPolynomial_coeff_zero_ne_zero
    (D : FinitePrimeChainData N) (lam : ℝ) :
    (partitionPolynomial D lam).coeff 0 ≠ 0 := by
  rw [partitionPolynomial_coeff_zero_eq_real_sum]
  exact_mod_cast (ne_of_gt (partitionPolynomial_coeff_zero_pos D lam))

theorem partitionPolynomial_ne_zero
    (D : FinitePrimeChainData N) (lam : ℝ) :
    partitionPolynomial D lam ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 0) hzero
  exact partitionPolynomial_coeff_zero_ne_zero D lam (by simpa using hcoeff)

theorem partitionFunction_zero_eq_coeff_zero
    (D : FinitePrimeChainData N) (lam : ℝ) :
    partitionFunction D lam 0 = (partitionPolynomial D lam).coeff 0 := by
  unfold partitionFunction
  exact (Polynomial.coeff_zero_eq_eval_zero (partitionPolynomial D lam)).symm

theorem partitionFunction_zero_ne_zero
    (D : FinitePrimeChainData N) (lam : ℝ) :
    partitionFunction D lam 0 ≠ 0 := by
  rw [partitionFunction_zero_eq_coeff_zero]
  exact partitionPolynomial_coeff_zero_ne_zero D lam

end InfoGeometry.Canonical.PrimePartitionPolynomialFinitePositivityBridge
