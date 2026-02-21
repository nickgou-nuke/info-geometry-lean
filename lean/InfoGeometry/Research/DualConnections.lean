import InfoGeometry.Assumptions.DualConnections
import InfoGeometry.Information.MultiLogPotential

/-!
# Research.DualConnections

Domain module for dual-connection geometry draft APIs extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- explicit scaffold interface from `InfoGeometry.Assumptions.DualConnections`
- constructive information-geometry context from `InfoGeometry.Information.MultiLogPotential`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.DualConnections

export InfoGeometry.Assumptions.DualConnections (
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  fisher_metric_eq_hessian_KL
)

end InfoGeometry.Research.DualConnections

