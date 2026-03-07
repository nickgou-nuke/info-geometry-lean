# Deep Horizon Synthesis

This note summarizes the deep-horizon canonical stack now exposed through
`InfoGeometry.Canonical.DeepHorizon`.

## Chain Overview

1. Grand-canonical routing:
   Sinkhorn-balanced router switches decompose into permutation simplices.
2. Split-Clifford lift:
   permutation modes carry `Cl(1,1)` semantic labels and modewise Dirac data.
3. Cayley transport:
   dual-flat Bregman geometry transports between unbounded and bounded charts
   with Pythagorean invariance.
4. Tomita-Takesaki atom:
   the modular generators `{1, J, ε, Jε}` generate the split Clifford algebra.
5. Holographic emergence:
   time-flow monotonicity, anomaly scale phase, torsion/hysteresis, and
   boundary-to-twistor closure are packaged constructively.

## Canonical Route In Code

1. `Canonical/GrandCanonicalExperts.lean`:
   permutation decomposition, split-Clifford mode states, Dirac mode operators.
2. `Canonical/CayleyBregmanBridge.lean`:
   Cayley bridge structures and `cayleyPythagoreanInvariance`.
3. `Canonical/TomitaTakesaki.lean`:
   modular atom and split `Cl(1,1)` generation theorem.
4. `Canonical/HolographicEmergence.lean`:
   consolidated emergence package and twistor-boundary closure lemmas.
5. `Canonical/DeepHorizon.lean`:
   publication facade exporting the synthesis interface.

## Canonical Entry Point

- `InfoGeometry.Canonical.DeepHorizon`
