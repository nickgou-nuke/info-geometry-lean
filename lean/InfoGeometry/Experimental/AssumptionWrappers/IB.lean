import InfoGeometry.Assumptions.IB

/-!
# Experimental.AssumptionWrappers.IB

Experimental wrapper over `InfoGeometry.Assumptions.IB`.
This is the canonical migration home for legacy `Research.IB` forwarding.
-/

namespace InfoGeometry.Experimental.AssumptionWrappers.IB

export InfoGeometry.Assumptions.IB (
  FinProb
  IBProblem
  KLKernel
  mutualInformation
  jointYT
  inducedMProjection
  energy
  partitionFunction
  exponentialTilt
  argmin_exponentialTilt
  argmin_exponentialTilt_true
  ibLagrangian
  ibIteration
  ib_stationary_point_gibbs
  ib_stationary_point_gibbs_true
  ib_convergence
  ib_convergence_true
  ib_convergence_nonneg
)

end InfoGeometry.Experimental.AssumptionWrappers.IB

