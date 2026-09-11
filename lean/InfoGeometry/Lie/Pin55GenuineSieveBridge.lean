import InfoGeometry.Lie.Pin55KreinConformalBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.GenuineBounds
import InfoGeometry.Lie.SpinorEquiv
import Omega.Zeta.XiChainInteriorIncidenceAlgebraMobiusInversion

namespace InfoGeometry.Lie.Pin55GenuineSieveBridge

open InfoGeometry.Lie.Pin55KreinConformalBridge
open InfoGeometry.Arithmetic.GenuineBounds
open InfoGeometry.Lie.SpinorEquiv
open Omega.Zeta

set_option linter.unusedVariables false

/--
The installed Pin(5,5) package is independent of the arithmetic estimate.
Under explicit package hypotheses this adapter returns the native
Rosser--Schoenfeld bound; it asserts no sieve/conformal correspondence.
-/
theorem prime_count_bound_with_installed_package
    (_pkg : Pin55KreinConformalPackage)
    (_hcompat : Pin55FiniteCarrierCompatibility)
    (x : ℕ) (hx : x ≥ 55) :
    (Nat.primeCounting x : ℝ) ≤ (x : ℝ) + 1 := by
  exact rosser_schoenfeld_prime_count_bound x hx

end InfoGeometry.Lie.Pin55GenuineSieveBridge
