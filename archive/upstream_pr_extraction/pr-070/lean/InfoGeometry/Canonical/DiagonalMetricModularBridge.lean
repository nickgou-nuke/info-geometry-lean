/-
InfoGeometry/Canonical/DiagonalMetricModularBridge.lean

The former owner specialized a Hessian metric to a scalar diagonal slice
`c • id` on a doubled carrier.  Although its readouts were kernel-checked,
that construction is not a noncommutative metric theorem and has no
maintained declaration consumers.

Use the native operatorial owners instead:

* `CoordinatelessSouriauKMSBridge` for state/observable Fisher-SLD data;
* `RelativeModularOperator` and `RelativeSurprisalOperatorLift` for relative
  modular/surprisal operators;
* `DiracMetricCompatibility` and `KreinDiracPolarizationBridge` for genuine
  operator square-root and polarization transport statements.

This file is an import-routing marker only.  It exports no scalar-diagonal
replacement API and makes no continuum or Tomita identification claim.
-/

import InfoGeometry.Canonical.CoordinatelessSouriauKMSBridge
import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.DiracMetricCompatibility
import InfoGeometry.Canonical.KreinDiracPolarizationBridge

namespace InfoGeometry.Canonical.DiagonalMetricModularBridge

/- The former diagonal specialization is retired; use the native owners above. -/

end InfoGeometry.Canonical.DiagonalMetricModularBridge
