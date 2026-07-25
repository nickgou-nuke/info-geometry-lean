import Mathlib
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/-!
# Prime Lee-Yang RH Conformal Bridge

This module supplies the theorem-honest adapter between:

* a root of the concrete partition polynomial stored by
  `PrimeFerromagneticChain.LeeYangStabilityWitness`;
* an externally established Lee--Yang circle theorem for that polynomial; and
* the Cayley equivalence proved in `CayleyCriticalLineCircleBridge`.

It does not prove the Lee--Yang circle theorem.  It also does not identify a
partition-polynomial root with a zero of the Riemann zeta function and makes no
Riemann-hypothesis claim.
-/

noncomputable section

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

namespace InfoGeometry.Canonical.PrimeLeeYangRHBridge

/--
An actual root of a stored partition polynomial maps to the critical line,
provided a Lee--Yang root-location theorem has been proved for that polynomial.

The condition `z.re ≠ -1` removes the pole `z = -1` of
`cayleyToTemperature z = z / (1 + z)`.
-/
theorem partitionRoot_mapsToCriticalLine
    {n : ℕ}
    (W : LeeYangStabilityWitness (n := n))
    (hLeeYang :
      ∀ z : ℂ, W.partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    {z : ℂ}
    (hz : W.partitionPolynomial.IsRoot z)
    (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) := by
  exact cayleyToTemperature_mem_criticalLine_of_unitCircle z
    (W.root_lies_on_leeYang_circle hLeeYang z hz) hpole

/--
For a non-polar partition root satisfying the Lee--Yang theorem, the Cayley
coordinate lies on the critical line and transforming back recovers the
original root.

This is the exact finite algebraic content of the Lee--Yang/critical-line
coordinate dictionary.  No statement about zeta zeros is used.
-/
theorem partitionRoot_cayleyRoundTrip
    {n : ℕ}
    (W : LeeYangStabilityWitness (n := n))
    (hLeeYang :
      ∀ z : ℂ, W.partitionPolynomial.IsRoot z → OnLeeYangCircle z)
    {z : ℂ}
    (hz : W.partitionPolynomial.IsRoot z)
    (hpole : z.re ≠ -1) :
    OnCriticalLine (cayleyToTemperature z) ∧
      cayleyToFugacity (cayleyToTemperature z) = z := by
  constructor
  · exact partitionRoot_mapsToCriticalLine W hLeeYang hz hpole
  · apply cayleyToFugacity_cayleyToTemperature
    intro hzero
    have hre : (1 + z).re = 0 := by rw [hzero]; simp
    have h_re : z.re = -1 := by
      calc z.re = (1 + z).re - 1 := by simp
      _ = 0 - 1 := by rw [hre]
      _ = -1 := by ring
    exact hpole h_re

end InfoGeometry.Canonical.PrimeLeeYangRHBridge
