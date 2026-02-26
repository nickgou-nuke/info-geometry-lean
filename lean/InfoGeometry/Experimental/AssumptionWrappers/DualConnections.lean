import InfoGeometry.Assumptions.DualConnections

/-!
# Experimental.AssumptionWrappers.DualConnections

Experimental wrapper over `InfoGeometry.Assumptions.DualConnections`.
This is the canonical migration home for legacy `Research.DualConnections` forwarding.
-/

namespace InfoGeometry.Experimental.AssumptionWrappers.DualConnections

export InfoGeometry.Assumptions.DualConnections (
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  fisherMetric_of_finProb
  amariChentsovTensor_of_finProb
  fisher_metric_eq_hessian_KL
)

end InfoGeometry.Experimental.AssumptionWrappers.DualConnections

