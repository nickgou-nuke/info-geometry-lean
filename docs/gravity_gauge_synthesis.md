# Gravity Gauge Synthesis

This note summarizes the canonical synthesis between kinematics, Einstein-scale
gravity bridges, and Weyl gauge scaling in the InfoGeometry Lean stack.

## Chain Overview

1. Kinematics and thermal vacuum:
   Bogoliubov mixing deforms doubled-state creation/annihilation channels.
2. Grand-canonical deformation:
   Einstein residual transport shifts the effective chemical potential.
3. Einstein-Kahler closure:
   Monge-Ampere constraints and anomaly sourcing close curvature equations.
4. Cartan algebraic split:
   symmetric-Lie decomposition isolates compact/boost channels.
5. Weyl gauge scaling:
   Sinkhorn balancing acts as a two-sided gauge scaling law.
6. Projective conformal quotient:
   ray-level collapse captures scale-invariant physical observables.

## Canonical Route In Code

1. `Canonical/BogoliubovFockSuper.lean`:
   Bogoliubov parameters, grand-canonical generator, Einstein-Fock deformation.
2. `Canonical/CalabiYauBridge.lean` and `Canonical/ChiralEinsteinBridge.lean`:
   Monge-Ampere to Ricci/vacuum-Einstein bridges with anomaly coupling.
3. `Core/SymmetricLieGeneric.lean` and `Canonical/SpinConnection.lean`:
   Cartan split laws and transport-connection structure.
4. `Canonical/WeylInformationGauge.lean`:
   Sinkhorn-to-Weyl gauge equivalence.
5. `Projective/Dynamics.lean`:
   projective ray quotient and conformal collapse behavior.

## Canonical Entry Points

- `InfoGeometry.Canonical.BogoliubovFockSuper`
- `InfoGeometry.Canonical.ChiralEinsteinBridge`
- `InfoGeometry.Canonical.SpinConnection`
- `InfoGeometry.Canonical.WeylInformationGauge`
