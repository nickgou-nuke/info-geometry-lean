import Mathlib

/-!
# Prime Wavelet MRA

Small compiled owner surface for dyadic/prime-scale wavelet weights.

This file intentionally avoids analytic claims about an `L²` multiresolution
analysis. It provides the finite arithmetic scale data used by the wavelet
namespace and leaves Hilbert-space MRA constructions to downstream owner files.
-/

namespace InfoGeometry.Wavelet.PrimeWaveletMRA

/-- Dyadic scale at level `n`. -/
def dyadicScale (n : ℕ) : ℕ :=
  2 ^ n

@[simp]
theorem dyadicScale_zero :
    dyadicScale 0 = 1 := by
  simp [dyadicScale]

/-- Successive dyadic scales double. -/
theorem dyadicScale_succ (n : ℕ) :
    dyadicScale (n + 1) = 2 * dyadicScale n := by
  simp [dyadicScale, pow_succ, Nat.mul_comm]

/--
Prime-filtered wavelet weight.

Non-prime carriers have zero weight; prime carriers retain their scale power.
-/
def primeWaveletWeight (p n : ℕ) : ℕ :=
  if Nat.Prime p then p ^ n else 0

@[simp]
theorem primeWaveletWeight_of_prime
    {p n : ℕ} (hp : Nat.Prime p) :
    primeWaveletWeight p n = p ^ n := by
  simp [primeWaveletWeight, hp]

@[simp]
theorem primeWaveletWeight_of_not_prime
    {p n : ℕ} (hp : ¬ Nat.Prime p) :
    primeWaveletWeight p n = 0 := by
  simp [primeWaveletWeight, hp]

@[simp]
theorem primeWaveletWeight_zero_level
    {p : ℕ} (hp : Nat.Prime p) :
    primeWaveletWeight p 0 = 1 := by
  simp [primeWaveletWeight, hp]

end InfoGeometry.Wavelet.PrimeWaveletMRA
