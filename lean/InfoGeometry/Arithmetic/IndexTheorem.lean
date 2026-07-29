import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Geometry.SpectralDivisors

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
