import InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Retired scalar Radon--Nikodym transport facade

The former contents of this path were a two-real-coordinate exponential
contraction and a hand-written rotor norm identity.  They did not define a
Radon--Nikodym derivative, a measure transport, or a noncommutative modular
cocycle.  The maintained owners are the finite relative-surprisal operator,
the operatorial Hessian/Kubo--Mori readout, and the real Bogoliubov transport.

Downstream code must use those typed operator interfaces; no scalar transport
or colimit theorem is exported from this compatibility path.
-/

namespace InfoGeometry.InformationGeometry.RadonNikodym

end InfoGeometry.InformationGeometry.RadonNikodym
