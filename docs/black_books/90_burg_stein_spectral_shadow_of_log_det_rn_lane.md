# Log-det Potentials, Burg Divergence, and Modular Hamiltonians

## Executive Thesis

The finite-dimensional SPD divergence

`D_B(P || Q) = tr(Q^{-1} P) - log det(Q^{-1} P) - n`

is the sharp classical shadow of the repository's noncommutative
multiplicative-to-additive mechanism:

1. multiplicative chain law (RN / determinant / cocycle),
2. abelian scalar descent,
3. additive log-potential readout.

`log-det` geometry is an abelian shadow of modular theory, not the Type-III
owner itself.

The canonical convex atom is

`f(lambda) = lambda - log lambda - 1`,

which drives positivity, asymmetry, and spectral normal form.

## I. Burg/Stein as the SPD Log-det Bregman Potential

On the SPD cone `S_{++}^n`, take the strictly convex potential

`zeta(C) = -log det C`.

Its Bregman divergence yields Burg/Stein loss:

`B(P, Q) = tr(P Q^{-1}) - log det(P Q^{-1}) - n`.

This is the exact finite lane where log-det acts as an additive potential:
the divergence is the affine linearization error of `-log det`.

## II. Spectral Normal Form

For `P, Q` SPD, define

`R = Q^{-1/2} P Q^{-1/2}`.

`R` is SPD with positive eigenvalues `lambda_i`, and

`D_B(P || Q) = sum_i f(lambda_i)`,

with `f(lambda) = lambda - log lambda - 1`.

Consequences:

- `f` is strictly convex on `(0, infinity)`.
- `f(1) = 0` and `f(lambda) >= 0`.
- `D_B(P || Q) >= 0`, equality iff `P = Q`.

So Burg/Stein is a spectral sum of one scalar convex kernel.

## III. Directionality and Congruence Invariance

### Asymmetry

Swapping inputs inverts the relative spectrum:

- `eig(P^{-1/2} Q P^{-1/2}) = lambda_i^{-1}`.

Since `f(lambda) != f(lambda^{-1})` in general,

`D_B(P || Q) != D_B(Q || P)`.

This finite asymmetry is the classical shadow of directional relative modular
comparisons.

### Congruence invariance

For invertible `M`, replacing

- `P -> M P M^T`,
- `Q -> M Q M^T`,

preserves the relative spectrum up to similarity, so Burg/Stein is invariant
under coordinate change and is natural on SPD geometry.

## IV. Gaussian KL Bridge (Finite Shadow)

For multivariate Gaussians, the covariance contribution of KL is exactly the
trace-minus-logdet expression (up to the standard one-half factor and
orientation convention):

`D_KL(N(m_p,P) || N(m_q,Q))`
`= 1/2 * [ tr(Q^{-1} P) + (m_q-m_p)^T Q^{-1} (m_q-m_p) - log det(Q^{-1} P) - n ]`.

When means match, Burg/Stein is the covariance skeleton of Gaussian KL.

## V. Noncommutative Lift: Relative Modular Operator Primary

The Type-III/operator-algebraic lift keeps multiplicative objects primary.

Owner order:

1. `Delta_{psi|phi}` primary (relative modular operator / RN-like owner),
2. `K_{psi|phi} := -log Delta_{psi|phi}` derived by spectral functional
   calculus (support/domain aware),
3. scalar readout as state/weight pairing (GNS; natural cone in standard form),
4. cocycle chain law primary (multiplicative), additive log structure derived
   from its generator where defined.

Scalarization hierarchy:

- finite: `-log det` shadows,
- semifinite: trace pairings like `Tr(-log Delta)` when available,
- Type III: no determinant/trace owner in general; `Delta` and `log Delta`
  remain primary operators.

This avoids the false rule `log(AB) = log A + log B` at raw operator level.

## VI. First-Quantization Dictionary (Repo Lane)

Classical -> modular dictionary:

- density ratio `p/q` -> relative modular operator `Delta_{phi,psi}`,
- surprisal `-log(p/q)` -> relative modular Hamiltonian `-log Delta_{phi,psi}`,
- expectation under density -> state/weight pairing (GNS; natural cone only in
  standard-form realization),
- RN/Jacobian chain rule -> Connes cocycle (multiplicative), with additive
  structure from the logarithmic generator where defined.

This is the mathematically honest translation layer from commutative
log-det/RN mechanics to noncommutative modular dynamics.

## VII. Canonical Guardrail

In Type III, only `Delta` and `log Delta` are canonical at the owner level;
all scalarizations are representation-dependent shadows.

## VIII. Repo Anchors

RN / determinant / cocycle ownership:

- [relativeDensity_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:37)
- [relativeModularOperator_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:46)
- [connesCocycle_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:120)

Delta-primary to Hamiltonian finite/support lane:

- [relativeModularOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:100)
- [relativeModularHamiltonianOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:100)
- [deltaFiniteSupportShadow](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/ConnesCocycleDeltaPrimaryBridge.lean:43)

Log-det mechanism packaging:

- [TypeIIILogDetRNPackage](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean:69)

## IX. Boundary Law

This chapter formalizes the finite SPD and finite/support operator-owner
bridge. It does not claim full unbounded affiliated-operator closure for
`K = -log Delta` in general Type-III owner form. That remains the open
continuous-core queue.
