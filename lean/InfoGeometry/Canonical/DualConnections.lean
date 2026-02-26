import InfoGeometry.Experimental.AssumptionWrappers.DualConnections

/-!
# Research.DualConnections

Compatibility forwarder over
`InfoGeometry.Experimental.AssumptionWrappers.DualConnections`.
-/

namespace InfoGeometry.Canonical.DualConnections

/-!
Explicitly forward the dual-connection scaffold surface from the
experimental wrapper.
-/
export InfoGeometry.Experimental.AssumptionWrappers.DualConnections (
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  fisherMetric_of_finProb
  amariChentsovTensor_of_finProb
  fisher_metric_eq_hessian_KL
)

end InfoGeometry.Canonical.DualConnections
