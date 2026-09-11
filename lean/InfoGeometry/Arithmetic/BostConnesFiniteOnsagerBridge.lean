import InfoGeometry.Arithmetic.BostConnesFiniteFisherBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Retired scalar Onsager wrapper

The former contents repackaged one finite variance as a scalar map
`ℝ →ₗ[ℝ] ℝ` with the commutative pairing `x * y`.  That is not a native
noncommutative Onsager construction and added no downstream theorem beyond the
finite variance owner.

The maintained finite result is
`InfoGeometry.Arithmetic.BostConnesFiniteFisherBridge`; genuine operatorial
Onsager/modular response belongs to the existing `RelativeModularPotential`
and `SouriauModularBregmanOperator` owners.
-/
