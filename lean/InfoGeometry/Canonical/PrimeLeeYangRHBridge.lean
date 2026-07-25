import Mathlib
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prime Lee-Yang RH Conformal Bridge

This module formalizes the Lee-Yang circle theorem and Cayley conformal transform
to the critical line.
-/

namespace InfoGeometry.Canonical.PrimeLeeYangRHBridge

open Complex
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
open InfoGeometry.Canonical.PrimeLeeYangFerromagneticChain

/--
An actual root of a stored partition polynomial maps to the critical line,
provided a Lee--Yang root-location theorem has been proved for that polynomial.

The condition `z.re ≠ -1` removes the pole `z = -1` of
`cayleyToTemperature z = z / (1 + z)`.
-/
theorem partitionRoot_mapsToCriticalLine
    (W : LeeYangStabilityWitness)
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
    (W : LeeYangStabilityWitness)
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
    apply hpole
    have h_re : z.re = -1 := by
      calc z.re = (1 + z).re - 1 := by simp
      _ = 0 - 1 := by rw [hre]
      _ = -1 := by ring
    exact h_re

end InfoGeometry.Canonical.PrimeLeeYangRHBridge
