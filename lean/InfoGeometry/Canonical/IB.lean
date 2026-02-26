import InfoGeometry.Experimental.AssumptionWrappers.IB

/-!
# Research.IB

Compatibility forwarder over `InfoGeometry.Experimental.AssumptionWrappers.IB`.
-/

namespace InfoGeometry.Canonical.IB

/-!
Explicitly forward the IB scaffold surface from the experimental wrapper.
-/
export InfoGeometry.Experimental.AssumptionWrappers.IB (
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

end InfoGeometry.Canonical.IB
