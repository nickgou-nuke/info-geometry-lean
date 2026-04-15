# Burg-Stein Spectral Shadow of the Log-Det RN Lane

## Executive Thesis

The finite-dimensional SPD divergence

`D_B(P || Q) = tr(Q^{-1} P) - log det(Q^{-1} P) - n`

is the sharp classical shadow of the repository's noncommutative
multiplicative-to-additive mechanism:

1. multiplicative chain law (RN / determinant / cocycle),
2. abelian scalar descent,
3. additive log-potential readout.

## I. Spectral Core of the Burg/Stein Potential

For `P, Q` symmetric positive definite, write the generalized spectrum
`lambda_i = eig(Q^{-1/2} P Q^{-1/2})`, then:

`D_B(P || Q) = sum_i (lambda_i - log lambda_i - 1)`.

The scalar kernel `f(lambda) = lambda - log lambda - 1` has:

- strict convexity on `(0, infty)`,
- unique minimum `f(1) = 0`,
- positivity `f(lambda) >= 0`.

Hence `D_B(P || Q) >= 0`, with equality iff `P = Q`.

## II. Directionality (Asymmetry)

Swapping inputs inverts spectral values:

- `eig(P^{-1/2} Q P^{-1/2}) = lambda_i^{-1}`.

Since

- `lambda - log lambda - 1 != lambda^{-1} + log lambda - 1`,

we get `D_B(P || Q) != D_B(Q || P)` in general.

This is the finite-lane analogue of directed relative modular data: the
relative object is oriented from reference state to comparison state.

## III. Congruence Invariance (Natural Geometry)

For invertible `M`,

- `P -> M P M^T`,
- `Q -> M Q M^T`,

preserves the spectrum of `Q^{-1} P` up to similarity. Therefore `D_B` is
congruence-invariant and is natural on the SPD quotient geometry.

## IV. Gaussian KL Identity (Classical Information Bridge)

In the centered Gaussian covariance lane, the KL divergence reduces to the same
trace-minus-logdet expression, so Burg/Stein is not an analogy artifact but the
exact finite statistical realization of the log-det potential mechanism.

## V. Repo Owner Anchors

Primary noncommutative chain owners already compiled:

- [relativeDensity_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:37)
- [relativeModularOperator_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:46)
- [relativeModularVolumeShadow_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:58)
- [connesCocycle_state_chain](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RNDeterminantConnesChainBridge.lean:120)

Delta-primary / additive-potential owners:

- [relativeModularOperator](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:100)
- [relativeModularVolumePotential](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularOperator.lean:235)
- [relativeModularHamiltonianExpectation_eq_inv_card_mul_relativeModularVolumePotential](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean:135)

Unified packaging layer for this chapter's mechanism:

- [TypeIIILogDetRNPackage](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean:69)
- [TypeIIILogDetRNPackage.logPotential_add](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean:82)
- [TypeIIILogDetRNPackage.cocycle_chain_rule](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Canonical/LogDetRadonNikodymMechanism.lean:88)

Finite thermodynamic/log-det lane:

- [energyFromLogDet](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Thermo/FromLogDet.lean:16)
- [freeEnergyFromLogDet](/home/goutev/LEAN4/info-geometry-lean/lean/InfoGeometry/Thermo/FromLogDet.lean:29)

## VI. Boundary Law

This chapter is a finite SPD spectral closure statement. It does not claim full
unbounded affiliated-operator `log Delta` closure in Type III generality.
That lane remains continuous-core / modular-owner work.

## VII. Applied Lane Targets

Direct computational targets for this exact divergence surface:

1. covariance estimation and shrinkage scoring on SPD cones,
2. matrix-valued optimal transport regularization with log-det barriers,
3. finite-dimensional quantum state tomography in covariance-like parameter
   charts.
