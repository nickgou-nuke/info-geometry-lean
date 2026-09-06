import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Geometry.SpectralDivisors
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite arithmetic grading packet for the index lane

This file exposes only kernel-checked arithmetic identities already proved in
`BostConnesSystem`. It does not prove a Witten-index/Euler-characteristic
identification, ζ-regularized supersymmetry statement, or anomaly-cancellation
theorem.
-/

namespace InfoGeometry.Arithmetic.IndexTheorem

open scoped BigOperators
open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors

/-- The total prime-factor count of `1` is zero. -/
@[simp] theorem totalPrimeFactors_one :
    totalPrimeFactors 1 = 0 :=
  InfoGeometry.Arithmetic.BostConnesSystem.totalPrimeFactors_one

/-- A prime contributes exactly one prime factor. -/
theorem totalPrimeFactors_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    totalPrimeFactors p = 1 :=
  InfoGeometry.Arithmetic.BostConnesSystem.totalPrimeFactors_prime p hp

/-- The Liouville grading is trivial on the vacuum. -/
@[simp] theorem liouville_one :
    liouville 1 = 1 :=
  InfoGeometry.Arithmetic.BostConnesSystem.liouville_one

/-- The Liouville grading always squares to `1`. -/
theorem liouville_sq (n : ℕ+) :
    liouville n * liouville n = 1 :=
  InfoGeometry.Arithmetic.BostConnesSystem.liouville_sq n n.pos

/-- The Liouville grading is multiplicative. -/
theorem liouville_mul (m n : ℕ+) :
    liouville (m * n) = liouville m * liouville n :=
  InfoGeometry.Arithmetic.BostConnesSystem.liouville_mul m n m.pos n.pos m.ne_zero n.ne_zero

/-- On a prime, the Liouville grading is `-1`. -/
theorem liouville_prime (p : ℕ+) (hp : Nat.Prime p.val) :
    liouville p = -1 :=
  InfoGeometry.Arithmetic.BostConnesSystem.liouville_prime p hp

/-- Multiplication by a prime flips the Liouville sign. -/
theorem liouville_prime_mul (p n : ℕ+) (hp : Nat.Prime p.val) :
    liouville (p * n) = -liouville n :=
  InfoGeometry.Arithmetic.BostConnesSystem.liouville_prime_mul p n hp n.pos

/--
Compatibility readout for this lane.

The current repository proves the finite arithmetic grading identities above.
The following theorem only reads back equality supplied by the explicit
`TopologicalIndexDatum`; it is not a Witten-index, Euler-characteristic, or
anomaly-cancellation theorem.  A genuine identification with those objects
requires the finite graded complex and kernel correspondence provided by the
separate finite index owners.
-/
theorem topological_index_eq_spectral_flow
    {Region Point Tangent Value Cycle : Type*}
    [AddCommGroup Value] [Module ℝ Value]
    {I : GeometricIntegralBackend Region Point Tangent Value}
    {N : PhaseResidueNormalizer Value}
    {ω : OperatorOneForm Point Tangent Value}
    {W : WindingNumberDatum I N ω}
    (T : TopologicalIndexDatum I N ω W Cycle)
    (c : Cycle) :
    T.index c = T.spectralFlow c := by
  exact T.index_eq_spectralFlow c

/-! ## Finite graded index owner

The following is the genuine finite algebraic carrier for a two-term graded
complex.  It is intentionally independent of divisor data: a divisor-to-index
theorem requires an additional kernel/cokernel correspondence. -/

section FiniteGradedIndex

variable {K Vp Vm : Type*}
  [DivisionRing K]
  [AddCommGroup Vp] [Module K Vp]
  [AddCommGroup Vm] [Module K Vm]
  [FiniteDimensional K Vp] [FiniteDimensional K Vm]

/-- A finite two-term graded complex with odd maps in both directions. -/
structure FiniteTwoTermComplex where
  qPlus : Vp →ₗ[K] Vm
  qMinus : Vm →ₗ[K] Vp
  qMinus_qPlus : qMinus.comp qPlus = 0
  qPlus_qMinus : qPlus.comp qMinus = 0

/-- The finite Euler/Witten kernel index of a two-term complex. -/
noncomputable def finiteKernelIndex
    (C : FiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm)) : ℤ :=
  (Module.finrank K C.qPlus.ker : ℤ) - Module.finrank K C.qMinus.ker

/-! ## Finite signed divisor readout -/

/-- The signed integer charge of a finite marked divisor. -/
def finiteDivisorIndex {ι : Type*} (marks : Finset ι) (order : ι → ℤ) : ℤ :=
  ∑ a ∈ marks, order a

/-- The zero-differential two-term complex. -/
def zeroFiniteTwoTermComplex :
    FiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm) where
  qPlus := 0
  qMinus := 0
  qMinus_qPlus := by simp
  qPlus_qMinus := by simp

/-- For the zero complex, the kernel index is the graded dimension difference. -/
theorem finiteKernelIndex_zero :
    finiteKernelIndex
        (zeroFiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm)) =
      (Module.finrank K Vp : ℤ) - Module.finrank K Vm := by
  change (Module.finrank K (LinearMap.ker (0 : Vp →ₗ[K] Vm)) : ℤ) -
      Module.finrank K (LinearMap.ker (0 : Vm →ₗ[K] Vp)) =
      (Module.finrank K Vp : ℤ) - Module.finrank K Vm
  rw [LinearMap.ker_zero, LinearMap.ker_zero, finrank_top, finrank_top]

end FiniteGradedIndex

end InfoGeometry.Arithmetic.IndexTheorem
