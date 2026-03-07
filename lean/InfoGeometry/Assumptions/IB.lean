import InfoGeometry.Canonical.IB

/-!
# Assumptions.IB

DEPRECATED compatibility shim.

New code should import:
- `InfoGeometry.Canonical.IB`

Compatibility re-export of the canonical Information Bottleneck core.
This keeps legacy `InfoGeometry.Assumptions.IB.*` paths stable while removing
duplicated definitions.
-/

namespace InfoGeometry.Assumptions.IB

export InfoGeometry.Canonical.IB
  (FinProb
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
   ib_convergence_nonneg)

end InfoGeometry.Assumptions.IB
