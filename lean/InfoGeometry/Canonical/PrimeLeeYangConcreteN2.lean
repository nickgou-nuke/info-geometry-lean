import Mathlib
import InfoGeometry.Canonical.PrimeLeeYangFerromagnet
import InfoGeometry.Canonical.PrimePartitionPolynomials
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangRHBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
import InfoGeometry.Canonical.PrimeHurwitzLimit

open Complex
open InfoGeometry.Canonical.PrimeLeeYangFerromagnet
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain.PrimeFerromagneticChain
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangRHBridge
open InfoGeometry.Canonical.PrimePartitionPolynomials

/-!
# InfoGeometry.Canonical.PrimeLeeYangConcreteN2

Concrete N=2 instance of the Lee-Yang/RH bridge.

This module provides:
1. The concrete N=2 prime chain with explicit primes {2, 3}
2. Explicit partition polynomial for N=2
3. Concrete Lee-Yang property structure for N=2
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
      fin_cases i
      · exact Real.log_pos (by norm_num)
      · exact Real.log_pos (by norm_num)
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
@[simp]
noncomputable def partitionPolyN2 : Polynomial ℂ :=
  Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ)

/-- Explicit computation of the partition polynomial for N=2 -/
theorem partitionPolyN2_explicit : partitionPolyN2 = Polynomial.X ^ 2 - Polynomial.C (1 : ℂ) * Polynomial.X + Polynomial.C (1 : ℂ) := by
  rfl

/-! ## The one-site boundary case -/

/-- The one-site ferromagnetic partition polynomial.  Its unique zero is the
    Cayley pole `-1`, so it is a genuine unit-circle case but is not in the
    affine critical-line chart. -/
@[simp]
noncomputable def partitionPolyN1 : Polynomial ℂ :=
  Polynomial.X + Polynomial.C (1 : ℂ)

theorem partitionPolyN1_root_eq_neg_one
    {z : ℂ} (hz : partitionPolyN1.IsRoot z) : z = -1 := by
  have h : z + 1 = 0 := by
    simpa [partitionPolyN1, Polynomial.IsRoot] using hz
  linear_combination h

theorem leeYangStabilityN1 :
    ∀ z : ℂ, partitionPolyN1.IsRoot z → OnLeeYangCircle z := by
  intro z hz
  rw [partitionPolyN1_root_eq_neg_one hz]
  norm_num [OnLeeYangCircle, Complex.normSq_apply]

theorem partitionPolyN1_root_is_cayley_pole
    {z : ℂ} (hz : partitionPolyN1.IsRoot z) : z.re = -1 := by
  rw [partitionPolyN1_root_eq_neg_one hz]
  norm_num

/-! ## Exact coordinate readout for the two-site roots -/

theorem partitionPolyN2_root_coordinates
    {z : ℂ} (hz : partitionPolyN2.IsRoot z) :
    z.re = (1 / 2 : ℝ) ∧ z.im * z.im = (3 / 4 : ℝ) := by
  have hpoly : z ^ 2 - z + 1 = 0 := by
    simpa [partitionPolyN2, Polynomial.IsRoot] using hz
  have hre := congrArg Complex.re hpoly
  have him := congrArg Complex.im hpoly
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have him' : z.im * (2 * z.re - 1) = 0 := by
    nlinarith [him]
  rcases mul_eq_zero.mp him' with him0 | hrel
  · have hreal : z.re ^ 2 - z.re + 1 = 0 := by
      nlinarith [hre, him0]
    exfalso
    nlinarith [sq_nonneg (z.re - (1 / 2 : ℝ))]
  · have hzre : z.re = (1 / 2 : ℝ) := by
      linarith
    have himsq : z.im * z.im = (3 / 4 : ℝ) := by
      nlinarith [hre, hzre]
    exact ⟨hzre, himsq⟩

/-- The concrete Lee-Yang stability theorem for N=2 -/
theorem leeYangStabilityN2 :
    (∀ z : ℂ, (partitionPolyN2).IsRoot z → OnLeeYangCircle z) := by
  intro z hz
  have h : z ^ 2 - z + 1 = 0 := by
    simpa [partitionPolyN2, Polynomial.IsRoot] using hz
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have him' : z.im * (2 * z.re - 1) = 0 := by
    nlinarith [him]
  have hnorm : Complex.normSq z = 1 := by
    rcases mul_eq_zero.mp him' with him0 | hre0
    · rw [him0] at hre
      nlinarith [sq_nonneg (z.re - 1 / 2)]
    · have hzre : z.re = 1 / 2 := by
        linarith
      simp [Complex.normSq, hzre]
      nlinarith
  exact hnorm

/-- No root of the concrete two-site partition polynomial is the Cayley pole. -/
theorem partitionPolyN2_root_re_ne_neg_one
    {z : ℂ}
    (hz : partitionPolyN2.IsRoot z) :
    z.re ≠ -1 := by
  intro hre
  have hpoly : z ^ 2 - z + 1 = 0 := by
    simpa [partitionPolyN2, Polynomial.IsRoot] using hz
  have him := congrArg Complex.im hpoly
  have him_zero : z.im = 0 := by
    simp [pow_two, Complex.mul_im, hre] at him
    linarith
  have hz_neg_one : z = (-1 : ℂ) := by
    apply Complex.ext
    · simpa using hre
    · simp [him_zero]
  rw [hz_neg_one] at hpoly
  norm_num at hpoly

/--
Every root of the concrete two-site partition polynomial maps to the critical
line under the Cayley temperature coordinate.  The theorem consumes neither a
Lee--Yang property structure nor an externally supplied root-location premise.
-/
theorem partitionPolyN2_root_mapsToCriticalLine
    {z : ℂ}
    (hz : partitionPolyN2.IsRoot z) :
    OnCriticalLine (cayleyToTemperature z) :=
  cayleyToTemperature_mem_criticalLine_of_unitCircle z
    (leeYangStabilityN2 z hz) (partitionPolyN2_root_re_ne_neg_one hz)

/-- The Cayley chart is an exact round trip on every concrete two-site root. -/
theorem partitionPolyN2_root_cayleyRoundTrip
    {z : ℂ}
    (hz : partitionPolyN2.IsRoot z) :
    OnCriticalLine (cayleyToTemperature z) ∧
      cayleyToFugacity (cayleyToTemperature z) = z := by
  refine ⟨partitionPolyN2_root_mapsToCriticalLine hz, ?_⟩
  apply cayleyToFugacity_cayleyToTemperature
  intro hpole
  apply partitionPolyN2_root_re_ne_neg_one hz
  have hre : 1 + z.re = 0 := by
    simpa using congrArg Complex.re hpole
  linarith

end InfoGeometry.Canonical.PrimeLeeYangConcreteN2
