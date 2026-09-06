import InfoGeometry.OperatorAlgebra.ConnesSpatialDerivative
import InfoGeometry.OperatorAlgebra.NoncommutativeBogoliubovKANLift
import InfoGeometry.Canonical.RelativeModularBerezinianBridge

/-!
# Retired operator KL/BKM facade

The former declarations in this module stored scalar readouts and supplied
their defining equalities as fields.  They did not construct a KL functional,
a modular-flow integral, a BKM form, or a Type III expectation.

The maintained owners are now the noncommutative carriers imported above:
`BKMMetricDatum`, the Connes/spatial-derivative data, and the relative modular
Berezinian bridge.  This compatibility module intentionally exports no
surrogate theorem surface.
-/
