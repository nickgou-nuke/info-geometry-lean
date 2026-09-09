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

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Geometry.BilingualAnalyticity
open InfoGeometry.Geometry.SpectralDivisors

/-! ## Finite two-term complexes and their kernel index -/

/-- A finite two-term complex, with its two differentials and square-zero laws. -/
structure FiniteTwoTermComplex
    (K Vp Vm : Type*)
    [DivisionRing K] [AddCommGroup Vp] [AddCommGroup Vm]
    [Module K Vp] [Module K Vm] where
  qPlus : Vp →ₗ[K] Vm
  qMinus : Vm →ₗ[K] Vp
  qMinus_qPlus : qMinus.comp qPlus = 0
  qPlus_qMinus : qPlus.comp qMinus = 0

/-- Euler characteristic of the two-term complex, computed from kernels. -/
noncomputable def finiteKernelIndex
    {K Vp Vm : Type*}
    [DivisionRing K] [AddCommGroup Vp] [AddCommGroup Vm]
    [Module K Vp] [Module K Vm]
    [FiniteDimensional K Vp] [FiniteDimensional K Vm]
    (C : FiniteTwoTermComplex K Vp Vm) : ℤ :=
  (Module.finrank K (LinearMap.ker C.qPlus) : ℤ) -
    (Module.finrank K (LinearMap.ker C.qMinus) : ℤ)

/-- The zero-differential two-term complex on two finite-dimensional modules. -/
def zeroFiniteTwoTermComplex
    {K Vp Vm : Type*}
    [DivisionRing K] [AddCommGroup Vp] [AddCommGroup Vm]
    [Module K Vp] [Module K Vm] :
    FiniteTwoTermComplex K Vp Vm where
  qPlus := 0
  qMinus := 0
  qMinus_qPlus := by simp
  qPlus_qMinus := by simp

theorem finiteKernelIndex_zero
    {K Vp Vm : Type*}
    [DivisionRing K] [AddCommGroup Vp] [AddCommGroup Vm]
    [Module K Vp] [Module K Vm]
    [FiniteDimensional K Vp] [FiniteDimensional K Vm] :
    finiteKernelIndex (zeroFiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm)) =
      (Module.finrank K Vp : ℤ) - (Module.finrank K Vm : ℤ) := by
  unfold finiteKernelIndex
  rw [show (zeroFiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm)).qPlus = 0 by rfl,
    show (zeroFiniteTwoTermComplex (K := K) (Vp := Vp) (Vm := Vm)).qMinus = 0 by rfl]
  have hp : LinearMap.ker (0 : Vp →ₗ[K] Vm) = ⊤ := by
    ext x
    simp
  have hm : LinearMap.ker (0 : Vm →ₗ[K] Vp) = ⊤ := by
    ext x
    simp
  rw [hp, hm, finrank_top, finrank_top]

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
Open theorem debt for this lane.

The current repository proves the finite arithmetic grading identities above.
Any Witten-index, Euler-characteristic, or anomaly-cancellation statement must
be added later as a theorem with explicit operator/cohomological hypotheses.
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

end InfoGeometry.Arithmetic.IndexTheorem
