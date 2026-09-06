import InfoGeometry.Assumptions.DualConnections

/-!
# InfoGeometry.Canonical.DualConnections

Canonical dual-connection surface built directly from
`InfoGeometry.Assumptions.DualConnections`.
-/

namespace InfoGeometry.Canonical.DualConnections

/-!
Explicitly forward the dual-connection scaffold surface from the
assumptions layer.
-/
export InfoGeometry.Assumptions.DualConnections (
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  fisherMetric_of_finProb
  amariChentsovTensor_of_finProb
  fisher_metric_eq_hessian_KL
)

end InfoGeometry.Canonical.DualConnections
