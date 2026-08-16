import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Finite symmetric prime-log waves

This owner records only the finite algebraic part of the symmetric
`± log n` phase pairing.  It does not assert an infinite explicit formula,
convergence of a distribution, a spectral realization of zeta zeros, or RH.
The von Mangoldt weight is used directly, so prime powers are retained.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.SymmetricPrimeLogSpectrum

open scoped BigOperators

open Complex
open ArithmeticFunction

/-- Logarithmic frequency attached to a positive integer index. -/
def logFrequency (n : ℕ) : ℝ :=
  Real.log n

/-- The finite explicit-formula weight `Λ(n) / √n`. -/
def primeWeight (n : ℕ) : ℝ :=
  (Λ n : ℝ) / Real.sqrt n

/-- Opposite Fourier phases at frequencies `± y`. -/
def phasePair (t y : ℝ) : ℂ :=
  Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) +
    Complex.exp (-(((t * y : ℝ) : ℂ) * Complex.I))

/-- The opposite phases form a real cosine standing wave. -/
theorem phasePair_eq_two_cos (t y : ℝ) :
    phasePair t y = ((2 * Real.cos (t * y) : ℝ) : ℂ) := by
  simpa [phasePair] using
    (Complex.two_cos (((t * y : ℝ) : ℂ))).symm

/-- The paired phase is even in spectral time. -/
theorem phasePair_neg_time (t y : ℝ) :
    phasePair (-t) y = phasePair t y := by
  calc
    phasePair (-t) y =
        ((2 * Real.cos ((-t) * y) : ℝ) : ℂ) :=
      phasePair_eq_two_cos (-t) y
    _ = ((2 * Real.cos (t * y) : ℝ) : ℂ) := by
      rw [show (-t) * y = -(t * y) by ring]
      rw [Real.cos_neg]
    _ = phasePair t y :=
      (phasePair_eq_two_cos t y).symm

/-- A finite symmetric prime-log packet. -/
def finitePrimeWave (S : Finset ℕ) (t : ℝ) : ℂ :=
  S.sum (fun n =>
    (primeWeight n : ℂ) *
      phasePair t (logFrequency n))

/-- Every finite prime-log packet is even in spectral time. -/
theorem finitePrimeWave_neg (S : Finset ℕ) (t : ℝ) :
    finitePrimeWave S (-t) = finitePrimeWave S t := by
  unfold finitePrimeWave
  apply Finset.sum_congr rfl
  intro n hn
  rw [phasePair_neg_time]

end InfoGeometry.Arithmetic.SymmetricPrimeLogSpectrum

end noncomputable section
