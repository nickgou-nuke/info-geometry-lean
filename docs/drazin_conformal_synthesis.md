# Drazin Conformal Synthesis

This note summarizes the singular-boundary bridge between Drazin/Moore-Penrose
projectors, conformal closure, and chiral scale anomaly in the canonical stack.

## Chain Overview

1. Singular resolution:
   Drazin and Moore-Penrose inverses induce spectral and geometric projectors.
2. Boundary commutator:
   the chiral anomaly is the projector commutator on the degenerate sector.
3. Emergent scale:
   anomaly norm defines a nontrivial absolute scale parameter.
4. Conformal obstruction:
   positive anomaly breaks flat Weyl-weight closure.
5. Projective null boundary:
   degenerate Krein null rays identify the boundary where scale emerges.

## Canonical Route In Code

1. `Canonical/Drazin.lean`:
   Drazin inverse, projection, and splitting interfaces.
2. `Canonical/MoorePenrose.lean`:
   Moore-Penrose inverse and anomaly/scale definitions.
3. `Canonical/ConformalAlgebra.lean`:
   conformal generators and anomaly-driven closure obstruction theorem.
4. `Canonical/Projective.lean` and `Canonical/Krein.lean`:
   projective ray/null-cone boundary interfaces.

## Canonical Entry Points

- `InfoGeometry.Canonical.Drazin`
- `InfoGeometry.Canonical.MoorePenrose`
- `InfoGeometry.Canonical.ConformalAlgebra`
