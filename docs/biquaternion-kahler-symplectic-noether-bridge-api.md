# BiQuaternion Kahler Symplectic Noether Bridge API

Owner: `lean/InfoGeometry/Canonical/BiQuaternionKahlerSymplecticNoetherBridge.lean`

## What This File Proves

This bridge stays on the finite `R^4` carrier and proves:

- the Lagrangian/Killing symplectic readout is exactly `symplecticI`
- the bridged finite symplectic form is skew
- `I4c` is skew-adjoint for the finite dot product
- `I4c` is self-orthogonal in the finite dot product
- the finite Noether readback vanishes for the explicit invariant-potential premise
- the radial quadratic potential gives a zero finite Noether readback
- the quadratic Hamiltonian is invariant under the finite `I4c` rotation
- the torsion-quadratic action slot is exactly `(α / 4) * torsionNormFinite T`
- the action density with torsion norm inserted splits exactly as expected
- the Belinfante readout is symmetric locally in this bridge file
- the finite torsion-quadratic source is symmetric locally in this bridge file
- the finite source slot is symmetric when both summands are symmetric
- the Belinfante source corollary is therefore symmetric

## Scope Boundary

This file does not construct:

- smooth Killing fields
- Hamiltonian vector fields
- flows or moment maps
- continuum Noether currents
- continuum field dynamics

It is a finite algebraic bridge only.
