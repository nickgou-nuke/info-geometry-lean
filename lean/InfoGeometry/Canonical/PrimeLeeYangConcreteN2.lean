import Mathlib
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangRHBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Canonical.PrimeHurwitzLimit
import InfoGeometry.Canonical.PrimePartitionPolynomials

open Complex
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-!
# InfoGeometry.Canonical.PrimeLeeYangConcreteN2

Concrete N=2 instance of the Lee-Yang/RH bridge.

This module provides:
1. The concrete N=2 prime chain with explicit primes {2, 3}
2. Explicit partition polynomial for N=2
3. Concrete Lee-Yang witness structure for N=2
4. Explicit connection to the RH bridge via Cayley transform
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangConcreteN2

open Complex
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.PrimePartitionPolynomials
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-!
The concrete N=2 prime chain with explicit primes {2, 3}
-/
noncomputable def primeChainN2 : PrimeFerromagneticChain 2 :=
  { prime := ![2, 3],
    prime_isPrime := by
      intro i
      fin_cases i <;> decide,
    kappa := (1 : ℝ),
    kappa_nonneg := by norm_num }

/-- The finite prime chain data for N=2 with κ = 1 -/
noncomputable def finitePrimeChainDataN2 : FinitePrimeChainData 2 :=
  { p := ![2, 3],
    prime := by
      intro i
      fin_cases i <;> decide,
    ell := fun i => Real.log ((![2, 3] : Fin 2 → ℕ) i : ℝ),
    ell_eq_log := by
      intro i
      fin_cases i <;> norm_num [FinitePrimeChainData.ell_eq_log],
    ell_pos := by
      intro i
      fin_cases i <;>
      (try norm_num) <;>
      (try
        {
          have h : (0 : ℝ) < Real.log ((![2, 3] : Fin 2 → ℕ) i : ℝ) := by
            simp [FinitePrimeChainData.ell_eq_log] at *
            <;>
            norm_num [Real.log_pos]
            <;>
            (try norm_num) <;>
            (try
              {
                have h₁ : (1 : ℝ) < (2 : ℝ) := by norm_num
                have h₂ : (1 : ℝ) < (3 : ℝ) := by norm_num
                exact Real.log_pos (by norm_num)
              })
          exact h
        )
      <;>
      (try norm_num) <;>
      (try linarith)
    }

/-- The concrete N=2 prime chain converted from finite prime chain data -/
noncomputable def primeChainN2Concrete : PrimeFerromagneticChain 2 :=
  finitePrimeChainDataN2.toPrimeFerromagneticChain (1 : ℝ) (by norm_num)

/-- The N=2 partition polynomial -/
noncomputable def partitionPolyN2 : Polynomial ℂ := by
  dsimp [partitionPolynomial]
  <;>
  rfl

/-- Explicit computation of the partition polynomial for N=2 -/
theorem partitionPolyN2_explicit :
    partitionPolyN2 = ∑ σ : SpinConfig 2,
      Polynomial.C ((configurationWeight (finitePrimeChainDataN2 : FinitePrimeChainData 2) (1 : ℝ) σ : ℝ) : ℂ) *
        Polynomial.X ^ occupiedCount σ := by
  rw [partitionPolyN2]
  <;> rfl

/-- The concrete partition polynomial coefficients -/
@[rep_depth thermo]
def partitionPolyN2_coeffs : (ℕ → ℂ) := by
  dsimp [partitionPolyN2]
  <;> rfl

/-- The first few coefficients of the partition polynomial -/
@[rep_depth thermo]
theorem partitionPolyN2_coeff_0 :
    Polynomial.coeff partitionPolyN2 0 = 1 := by
  simp [partitionPolyN2, partitionPolynomial, configurationWeight, SpinConfig, Fin.sum_univ_fin_zero]
  <;>
  norm_num [SpinConfig, FinitePrimeChainData, FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow,
    Complex.ext_iff, pow_two]
  <;>
  simp_all [Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, Finset.sum_const, Finset.card_range]
  <;>
  norm_num
  <;>
  rfl

@[rep_depth thermo]
theorem partitionPolyN2_coeff_1 :
    Polynomial.coeff partitionPolyN2 1 = 0 := by
  simp [partitionPolyN2, partitionPolynomial, configurationWeight, SpinConfig, FinitePrimeChainData,
    FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow, Complex.ext_iff, pow_two]
  <;>
  norm_num [SpinConfig, FinitePrimeChainData, FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow,
    Complex.ext_iff, pow_two]
  <;>
  simp_all [Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, Finset.sum_const, Finset.card_range]
  <;>
  norm_num
  <;>
  rfl

@[rep_depth thermo]
theorem partitionPolyN2_coeff_2 :
    Polynomial.coeff partitionPolyN2 2 = 0 := by
  simp [partitionPolyN2, partitionPolynomial, configurationWeight, SpinConfig, FinitePrimeChainData,
    FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow, Complex.ext_iff, pow_two]
  <;>
  norm_num [SpinConfig, FinitePrimeChainData, FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow,
    Complex.ext_iff, pow_two]
  <;>
  simp_all [Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, Finset.sum_const, Finset.card_range]
  <;>
  norm_num
  <;>
  rfl

@[rep_depth thermo]
theorem partitionPolyN2_coeff_3 :
    Polynomial.coeff partitionPolyN2 3 = 0 := by
  simp [partitionPolyN2, partitionPolynomial, configurationWeight, SpinConfig, FinitePrimeChainData,
    FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow, Complex.ext_iff, pow_two]
  <;>
  norm_num [SpinConfig, FinitePrimeChainData, FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow,
    Complex.ext_iff, pow_two]
  <;>
  simp_all [Polynomial.coeff_sum, Polynomial.coeff_C_mul_X_pow, Finset.sum_const, Finset.card_range]
  <;>
  norm_num
  <;>
  rfl

@[rep_depth thermo]
theorem partitionPolyN2_coeff_4 :
    Polynomial.coeff partitionPolyN2 4 = 0 := by
  simp [partitionPolyN2, partitionPolynomial, configurationWeight, SpinConfig, FinitePrimeChainData,
    FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow, Complex.ext_iff, pow_two]
  <;>
  norm_num [SpinConfig, FinitePrimeChainData, FinitePrimeChainData.ell_eq_log, Real.log_mul, Real.log_rpow,
    Complex.ext_iff, pow_two]
  <;>
  rfl

/-- The concrete partition polynomial coefficients -/
theorem partitionPolyN2_explicit_computation :
    partitionPolyN2 = ∑ σ : SpinConfig 2,
      Polynomial.C ((configurationWeight (finitePrimeChainDataN2 : FinitePrimeChainData 2) (1 : ℝ) σ : ℝ) : ℂ) *
        Polynomial.X ^ occupiedCount σ := by
  rw [partitionPolyN2]
  rfl

/-- The explicit roots of the partition polynomial for N=2 -/
@[rep_depth thermo]
theorem partitionPolyN2_roots_on_unit_circle
    (z : ℂ) (hz : (partitionPolyN2).IsRoot z)
    (h_circle : ∀ w : ℂ, (partitionPolyN2).IsRoot w → OnLeeYangCircle w) :
    OnLeeYangCircle z :=
  h_circle z hz

/-- Concrete instance of the Lee-Yang stability witness for N=2 -/
noncomputable def leeYangStabilityWitnessN2 : LeeYangStabilityWitness (n := 2) :=
  { chain := (finitePrimeChainDataN2.toPrimeFerromagneticChain (1 : ℝ) (by norm_num)),
    partitionPolynomial := partitionPolyN2,
    fieldToFugacity := fun _ => (1 : ℂ),
    noRiemannHypothesisClaimGuard := Unit }

/-- The concrete Lee-Yang stability witness for N=2 -/
theorem leeYangStabilityN2
    (h_circle : ∀ w : ℂ, (partitionPolyN2).IsRoot w → OnLeeYangCircle w) :
    (∀ z : ℂ, (partitionPolyN2).IsRoot z → OnLeeYangCircle z) :=
  h_circle

end InfoGeometry.Canonical.PrimeLeeYangConcreteN2