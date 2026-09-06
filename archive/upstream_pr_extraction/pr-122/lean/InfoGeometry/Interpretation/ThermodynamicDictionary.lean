/-!
# InfoGeometry.Interpretation.ThermodynamicDictionary

Interpretive documentation layer for the canonical relative-geometry spine.

This module deliberately does not introduce a second API.
It exists so that generated documentation can present the formal mathematical
surfaces together with their preferred thermodynamic reading, while the kernel
itself remains expressed in the austere canonical language.

## Naming rule

- keep one formal Lean name in the core theory,
- keep one preferred physical alias in documentation,
- do not rename operator-level objects into thermodynamic scalars,
- treat the physical language as an interpretation of proved bridges, not as a
  replacement for them.

## Canonical spine

- `InfoGeometry.Canonical.RelativeWeight`
  physical alias: relative statistical weight
- `InfoGeometry.Canonical.LogGenerator`
  physical alias: logarithmic generating potential
- `InfoGeometry.Canonical.GeneratedFlow`
  physical alias: thermodynamic transport
- `InfoGeometry.Canonical.GeometricResponse`
  physical alias: information stress response or information susceptibility

## Partition and coarse graining

- `InfoGeometry.GrandCanonical.partition`
  physical alias: partition function
- `InfoGeometry.GrandCanonical.potential`
  physical alias: Massieu potential
- `InfoGeometry.GrandCanonical.gibbsWeight`
  physical alias: Gibbs weight
- `InfoGeometry.Canonical.PartitionHierarchy.fiberPartition`
  physical alias: effective partition function
- `InfoGeometry.Canonical.PartitionHierarchy.effectivePotential`
  physical alias: effective free-energy potential
- `InfoGeometry.Canonical.CoarseGraining.encoderMarginal`
  physical alias: coarse-grained marginal

## Anomaly and inverse-kernel dictionary

- `InfoGeometry.Canonical.CertifiedInverseKernel.spectralProjector`
  physical alias: spectral occupancy projector
- `InfoGeometry.Canonical.CertifiedInverseKernel.metricProjector`
  physical alias: metric occupancy projector
- `InfoGeometry.Canonical.CertifiedInverseKernel.projectorMismatch`
  physical alias: phase-space defect
- `InfoGeometry.Canonical.CertifiedInverseKernel.chiralAnomaly`
  physical alias: anomaly operator
- `InfoGeometry.Canonical.CertifiedInverseKernel.chiralScale`
  physical alias: anomaly chemical potential
- `InfoGeometry.Canonical.ConformalUnification.ConformalInference.unitOfAction`
  physical alias: effective Planck constant

The intended hierarchy is

`chiralAnomaly -> chiralScale -> effective thermodynamic source`

rather than a direct renaming of the operator anomaly itself into a chemical
potential.

## Modular and cocycle dictionary

- `InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.rnDerivative`
  physical alias: relative density
- `InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularOperator`
  physical alias: operator relative density
- `InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularHamiltonian`
  physical alias: logarithmic geometry-generating operator
- `InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData.modularAutomorphismGroup`
  physical alias: modular transport
- `InfoGeometry.Volume.ConnesCocycle.cocycleLogPotential`
  physical alias: scalar cocycle log-potential

## Flow-level responses

- `InfoGeometry.Canonical.GrandCanonicalExperts.SinkhornFlow.trajectoryRNBarrier`
  physical alias: entropic pressure barrier
- `InfoGeometry.Canonical.GrandCanonicalExperts.SinkhornFlow.trajectoryLyapunov`
  physical alias: transport Lyapunov objective
- `InfoGeometry.Canonical.PerelmanW.WFunctional`
  physical alias: geometric entropy functional
- `InfoGeometry.Canonical.PerelmanW.WDissipation`
  physical alias: geometric entropy dissipation

## Methodological note

This documentation layer is intentionally separate from
`InfoGeometry.Library`. The theorem-facing import surface remains mathematical.
The full public platform surface may re-export this module through
`InfoGeometry.All`, where the formal names and their canonical physical reading
can coexist without polluting the kernel-facing dependency graph.
-/

namespace InfoGeometry.Interpretation

end InfoGeometry.Interpretation
