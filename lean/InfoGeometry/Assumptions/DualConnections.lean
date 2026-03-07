import InfoGeometry.Canonical.DualConnections

/-!
# Assumptions.DualConnections

DEPRECATED compatibility shim.

New code should import:
- `InfoGeometry.Canonical.DualConnections`

Compatibility re-export of the canonical dual-connection layer.
This keeps legacy `InfoGeometry.Assumptions.DualConnections.*` paths stable while
removing duplicated definitions.
-/

namespace InfoGeometry.Assumptions.DualConnections

export InfoGeometry.Canonical.DualConnections (
  FiberTangent
  ConnectionTensor
  fisherBilinear
  fisherBilinear_comm
  fisherBilinear_self_nonneg
  chentsovTensor
  chentsovTensor_swap_left
  alphaConnectionTensor
  eConnectionTensor
  mConnectionTensor
  alphaConnectionTensor_zero
  alphaConnectionTensor_dual_sum
  alphaConnectionTensor_dual_diff
  e_m_connection_sum
  fisherMetric
  amariChentsovTensor
  alphaConnection
  alpha_duality
  alphaConnection_of_finProb
  fisherMetric_of_finProb
  amariChentsovTensor_of_finProb
  fisher_metric_eq_hessian_KL
)

export InfoGeometry.Canonical.DualConnections.alphaConnection (
  mkFromReference
  Gamma
  deformation_law
  dual
  undual
  dual_undual
  undual_dual
)

end InfoGeometry.Assumptions.DualConnections
