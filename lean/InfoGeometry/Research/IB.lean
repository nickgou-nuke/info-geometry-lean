import InfoGeometry.Assumptions.IB
import InfoGeometry.EntropicInference

/-!
# Research.IB

Domain module for the Information Bottleneck (IB) research API extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- constructive finite-probability primitives from `InfoGeometry.EntropicInference`
- IB draft interface from `InfoGeometry.Assumptions.IB`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.IB

export InfoGeometry.Assumptions.IB (
  IBProblem
  KLKernel
  jointYT
  inducedMProjection
  energy
  partitionFunction
  exponentialTilt
  argmin_exponentialTilt
  ibLagrangian
  ibIteration
  ib_stationary_point_gibbs
  ib_convergence
)

end InfoGeometry.Research.IB

