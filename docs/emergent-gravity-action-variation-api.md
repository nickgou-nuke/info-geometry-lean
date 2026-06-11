# Emergent Gravity Action Variation API

> Status: `finite shadow`
> Owner: `lean/InfoGeometry/Canonical/EmergentGravityActionVariation.lean`
> Related owners:
> - `lean/InfoGeometry/Canonical/EmergentGravity.lean`
> - `lean/InfoGeometry/Canonical/StressEnergyTensor.lean`

This page records the source-owned finite bridge for the emergent-gravity lane.

## What is proved

- `effectiveActionVariation` packages the finite action-density split into Dirac, mass, curvature, and torsion-norm terms.
- `effectiveActionVariation_zero_torsion` removes the torsion contribution when the torsion slot is zero.
- `effectiveActionVariation_torsion_split` isolates the torsion term as an additive contribution.
- `belinfanteReadout` re-exports the finite symmetric stress-energy readout from the owner tensor.
- `belinfanteReadout_symmetric` restates the symmetry of that finite Belinfante-style readout.

## What is not proved

- a continuum variational derivation of the Einstein-Cartan field equations
- a full curved-spacetime Dirac operator formalism
- a propagating torsion theory
- a global emergent-gravity theorem beyond the finite algebraic shadow

## Practical use

Use this module as the finite canonical endpoint for the action/stress-energy lane when you want:

- a source-faithful action-density split
- a symmetric Belinfante readout
- a safe bridge from the torsion sidecar into the stress-energy owner file
