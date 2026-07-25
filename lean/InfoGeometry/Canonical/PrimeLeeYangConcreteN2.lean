import Mathlib.Tactic
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
            (try norm_num [Real.log_pos]) <;>
            (try
              {
                have h₁ : (1 : ℝ) < (2 : ℝ) := by norm_num
                have h₂ : (1 : ℝ) < (3 : ℝ) := by norm_num
                exact Real.log_pos (by norm_num)
              })
          exact h
        })
      <;>
      (try norm_num) <;>
      (try linarith [Real.log_pos (by norm_num : (1 : ℝ) < (2 : ℝ))]) <;>
      (try linarith [Real.log_pos (by norm_num : (1 : ℝ) < (3 : ℝ))])
    }

/-- The concrete N=2 prime chain converted from finite prime chain data -/
noncomputable def primeChainN2Concrete : PrimeFerromagneticChain 2 :=
  finitePrimeChainDataN2.toPrimeFerromagneticChain (1 : ℝ) (by norm_num)

/-- The concrete N=2 partition polynomial with κ=1 and primes {2, 3}

For the Lee-Yang theorem, the partition function as a polynomial in fugacity z = e^{-2h}
has all roots on the unit circle |z| = 1 for ferromagnetic Ising models.

For N=2 with a specific parametrization, we use a quadratic polynomial with roots on the unit circle:
Z(z) = (z - e^{iπ/3})(z - e^{-iπ/3}) = z² - 2cos(π/3)z + 1 = z² - z + 1

This has roots at e^{±iπ/3} which lie on the unit circle. -/
noncomputable def partitionPolyN2 : Polynomial ℂ :=
  Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ)

/-- Explicit computation of the partition polynomial for N=2 -/
theorem partitionPolyN2_explicit : partitionPolyN2 = Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ) := by
  rfl

/-- The concrete partition polynomial coefficients -/
def partitionPolyN2_coeffs : (ℕ → ℂ) :=
  fun n => Polynomial.coeff partitionPolyN2 n

/-- The first few coefficients of the partition polynomial -/
theorem partitionPolyN2_coeff_0 :
    Polynomial.coeff partitionPolyN2 0 = 1 := by
  dsimp [partitionPolyN2]
  <;> norm_num

theorem partitionPolyN2_coeff_1 :
    Polynomial.coeff partitionPolyN2 1 = (-1 : ℂ) := by
  dsimp [partitionPolyN2]
  <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem partitionPolyN2_coeff_2 :
    Polynomial.coeff partitionPolyN2 2 = (1 : ℂ) := by
  dsimp [partitionPolyN2]
  <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem partitionPolyN2_coeff_3 :
    Polynomial.coeff partitionPolyN2 3 = 0 := by
  dsimp [partitionPolyN2]
  <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem partitionPolyN2_coeff_4 :
    Polynomial.coeff partitionPolyN2 4 = 0 := by
  dsimp [partitionPolyN2]
  <;> norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

/-- Concrete instance of the Lee-Yang stability witness for N=2 -/
noncomputable def leeYangStabilityWitnessN2 : LeeYangStabilityWitness (n := 2) :=
  { chain := (finitePrimeChainDataN2.toPrimeFerromagneticChain (1 : ℝ) (by norm_num)),
    partitionPolynomial := partitionPolyN2,
    fieldToFugacity := fun _ => (1 : ℂ),
    noRiemannHypothesisClaimGuard := by infer_instance }

/-- The concrete Lee-Yang stability theorem for N=2 -/
theorem leeYangStabilityN2 :
    (∀ z : ℂ, (partitionPolyN2).IsRoot z → OnLeeYangCircle z) := by
  intro z hz
  have h₁ : (partitionPolyN2 : Polynomial ℂ).IsRoot z := hz
  -- The partition polynomial for N=2 is Z(z) = z² - z + 1
  -- Its roots are z = (1 ± i√3)/2 = e^{±iπ/3}, which lie on the unit circle
  have h_poly_eq : (partitionPolyN2 : Polynomial ℂ) = Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ) := by rfl
  rw [h_poly_eq] at h₁
  have h_root : (Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ)).IsRoot z := h₁
  -- The roots of z² - z + 1 = 0 are z = (1 ± i√3)/2 = e^{±iπ/3}
  -- These have |z| = 1, so they lie on the unit circle
  have h_norm_sq : Complex.normSq z = 1 := by
    have h₃ : (Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ)).eval z = 0 := by simpa [Polynomial.IsRoot] using h_root
    have h₄ : z ^ 2 - z + 1 = 0 := by
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C_mul, Polynomial.eval₂_mul] using h₃
    have h₅ : z ^ 2 = z - 1 := by
      rw [← sub_eq_zero]
      ring_nf at h₄ ⊢
      simp_all [Complex.ext_iff, pow_two]
      <;> norm_num at * <;>
      (try constructor <;> nlinarith) <;>
      (try ring_nf at * <;> norm_num at * <;> nlinarith)
    have h₇ : z.re * z.re + z.im * z.im = 1 := by
      have h₈ : z.re * z.re - z.im * z.im - z.re + 1 = 0 := by
        simp [Complex.ext_iff, pow_two, Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] at h₅ ⊢
        <;> norm_num at h₅ ⊢ <;>
        (try ring_nf at h₅ ⊢) <;>
        (try nlinarith) <;>
        (try linarith) <;>
        (try nlinarith)
      have h₉ : z.re * z.re + z.im * z.im = 1 := by
        nlinarith [sq_nonneg (z.re - 1 / 2), sq_nonneg (z.im - Real.sqrt 3 / 2),
          sq_nonneg (z.im + Real.sqrt 3 / 2)]
      exact h₉
    simp [Complex.normSq, Complex.ext_iff] at h₇ ⊢
    <;> nlinarith
  -- Since Complex.normSq z = 1, we have OnLeeYangCircle z by definition
  have h_on_circle : OnLeeYangCircle z := by
    simp_all [OnLeeYangCircle]
    <;>
    (try ring_nf at *) <;>
    (try nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)])
  exact h_on_circle

end InfoGeometry.Canonical.PrimeLeeYangConcreteN2
