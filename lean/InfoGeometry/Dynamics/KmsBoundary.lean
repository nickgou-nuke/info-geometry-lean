import InfoGeometry.OperatorAlgebra.ModularWeightTrace
import InfoGeometry.OperatorAlgebra.ModularSignCPT
import InfoGeometry.Canonical.TomitaTakesakiModularFlow

/-!
# KMS boundary routing owner

The former finite diagonal `2 × 2` trace-cyclicity model has been retired.
It was only a commutative matrix shadow and did not formalize a KMS state on a
noncommutative algebra.  KMS/modular boundary work must use
`ModularWeightDatum`, `DynamicModularCPTAlgebra`, and the canonical
Tomita--Takesaki modular-flow owners imported above.

This marker intentionally exports no scalar replacement API.
-/

namespace InfoGeometry.Dynamics.KmsBoundary

end InfoGeometry.Dynamics.KmsBoundary
