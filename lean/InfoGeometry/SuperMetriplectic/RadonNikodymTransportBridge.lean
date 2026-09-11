import InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.SuperMetriplectic.CasimirHessianFisherBridge

/-!
# Retired scalar Radon--Nikodym transport surface

The former `HKState` implementation chose an affine contraction on `ℝ × ℝ`
and called its quadratic scaling a Radon--Nikodym transport.  It supplied no
measure, relative modular operator, or operatorial flow, so it is not a valid
RN theorem and is no longer exported.

Use the finite relative modular operator/potential owners for RN-surprisal
data, and `CasimirHessianFisherBridge` for observable-algebra Casimir and
positive-functional statements.  A genuine transport theorem must be stated
for those carriers with an explicit modular-flow or conjugation hypothesis.
-/

namespace InfoGeometry.SuperMetriplectic.RadonNikodymTransport

end InfoGeometry.SuperMetriplectic.RadonNikodymTransport
