# Finite chiral compatibility: owner reuse and scope

The new modules reuse the existing split-quaternion matrices, chiral involution,
Peirce projectors, Zorn BdG matrices, metriplectic flow, Krein adjoint, Jones
coordinates, Crawford Weyl gamma matrices and sixteen channel labels.
They do not modify the concurrent `ParahyperkahlerSpinBdG` draft.

## Dependency branches

- Split-quaternion grading -> native chiral involution -> equality with Peirce
  projectors -> pairing selection rules and explicit BdG representation.
- BdG representation -> squared operator identity and a lower bound for roots
  of its characteristic polynomial, conditional on the specified pairing.
- Existing metriplectic equilibrium plus an explicit BdG reversible component
  -> the same square identity for the total flow value. No trajectory,
  convergence, or unitarity is inferred from this equality.
- Existing braid matrix -> compatibility with native matrix multiplication,
  the complex grading, and fourth/eighth powers.
- Algebraic Krein adjoint -> exchange of principal left/right ideals ->
  supported operator-valued sandwiches -> existing Jones reconstruction.
- Sixteen Weyl Clifford channels -> trace-dual reconstruction -> reconstruction
  of a spinor dyad -> parity and vector-current selection rules.
- GL plus a specified Hermitian split metric -> metric-stabilizer subgroup;
  intersecting with the determinant homomorphism's kernel imposes determinant
  one. This is a subgroup construction, not a quotient of GL by dissipation.

## Conventions

`ChiralInvolution.Pleft` is the positive projector `(1 + chi)/2` in its owner;
the negative projector is `Pright`. These names do not silently change to the
opposite particle-physics convention. Principal ideals are not claimed minimal.

`DiracBilinearChannels` uses the existing **Weyl** matrices, not the distinct
Pauli-Dirac representation. Its insertions are `1`, `gamma5`, `gamma mu`,
`gamma mu * gamma5`, and `gamma mu * gamma nu` for the six ordered pairs
`mu < nu`. Conventional factors of `i` in tensor/pseudoscalar observables are
not silently inserted. Clifford degrees are 0, 4, 1, 3, and 2 respectively;
degree is not matrix rank or a claim of Lorentz covariance.

The reconstruction uses the Hilbert-Schmidt trace dual
`trace(channel.conjTranspose * operator)/4`. The spinor dyad is
`right * (left.conjTranspose * gamma0)`, so its coefficients are actual
Dirac bilinear readouts. The algebraic operator adjoint `eta * star A * eta`
and the spinor row adjoint `star psi * gamma0` remain distinct constructions.

## Boundaries and regressions

The test module records that the single Pauli raising operator has zero cube,
whereas its three-slot Kronecker product is nonzero. Neither is identified with
a spherical harmonic without an intertwiner into the appropriate representation.
An order-three equation alone does not eliminate the identity eigenspace.
No assertion that cyclic symmetry removes tensor traces or suppresses temporal
oscillation is included.

The selection rules do not supply a vacuum expectation, spontaneous symmetry
breaking, a pion effective action, a nuclear collision model, or a continuum
Yang-Mills construction. A nonzero scalar cross corner explicitly requires a
nonzero sector and an invertible metric witness.

## Verification

Full proof scripts and regression/axiom-report commands are present, but kernel
verification is pending: the pre-existing `lake build -R` owns the shared lane.
No concurrent compiler or test was started and no existing process was stopped.

When the lane is available:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.EmergentVacuum.CompatibilityTests
```

Until that succeeds, these additions are unverified source, not certified results.
