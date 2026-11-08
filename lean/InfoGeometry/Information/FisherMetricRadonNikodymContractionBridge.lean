import InfoGeometry.Canonical.RelativeSurprisalRadonNikodymBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Canonical.BogoliubovTransport

/-!
# Retired scalar Fisher/Radon--Nikodym contraction facade

The former implementation transported a hand-written scalar transverse
coordinate and called its square a Fisher/Radon--Nikodym contraction.  That
surface did not construct a measure, a modular operator, or a genuine Fisher
form.  The noncommutative replacement is provided by the relative-surprisal
operator and operatorial Hessian owners imported above, with Bogoliubov
transport supplied by its canonical owner.

This path is retained only for import compatibility and intentionally exports
no scalar state-flow API.
-/

namespace InfoGeometry.InformationGeometry.FisherMetric

end InfoGeometry.InformationGeometry.FisherMetric
