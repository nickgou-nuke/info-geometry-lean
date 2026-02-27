import InfoGeometry.Assumptions.IB

/-!
# InfoGeometry.Canonical.IB

Canonical IB surface built directly from `InfoGeometry.Assumptions.IB`.
-/

namespace InfoGeometry.Canonical.IB

/-!
Explicitly forward the IB scaffold surface from the assumptions layer.
-/
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

end InfoGeometry.Canonical.IB
