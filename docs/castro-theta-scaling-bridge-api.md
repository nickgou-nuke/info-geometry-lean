# Castro Theta Scaling Bridge API

Lean module:

- `lean/InfoGeometry/Arithmetic/CastroThetaScalingBridge.lean`

This module records the finite, theorem-backed fragment of the Castro
theta/scaling dictionary.  It avoids differentiable operator domains,
Hilbert-space completion, analytic theta modularity, and zeta-zero claims.

## Theorem Surface

- `modularSwap`
  swaps the two components of a doubled carrier.

- `doubledScaling`
  applies two channel maps diagonally on the doubled carrier.

- `modularSwap_involutive`
  proves the swap squares to the identity.

- `modularSwap_doubledScaling_modularSwap`
  proves that modular swap exchanges the two scaling channels.

- `thetaWeight`
  is a finite scalar Gauss-Jacobi-style weight in logarithmic coordinate.

- `finiteTheta`
  sums `thetaWeight` over a supplied finite index set.

- `thetaWeight_dual`
  proves the paired finite duality `l, tau -> -l, -tau` for one weight.

- `finiteTheta_dual`
  lifts that paired duality to any finite theta sum.

- `kronecker`
  is the real-valued finite Kronecker kernel.

- `finite_kronecker_resolution`
  proves the finite resolution-of-identity identity
  `sum_k delta(k,i) delta(k,j) = delta(i,j)`.

## Boundary

This is not a formalization of Castro's full Hilbert-Polya strategy.  It does
not prove self-adjointness, analytic theta modularity, a spectral trace
formula, completeness of scaling eigenfunctions, zeta-zero confinement, or the
Riemann Hypothesis.
