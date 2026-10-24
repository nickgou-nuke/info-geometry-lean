# Concrete tilt Gibbs completed-state consumer

Frozen scratch candidate: `TiltGibbsRepresentedNontracial20261024.lean`.
Planned native imports are `InfoGeometry.Canonical.FiniteMatrixGibbsNontracial`
and `InfoGeometry.Canonical.FilteredGNSNontracialReadback`.

For real `h, β` with `β * h ≠ 0`, use the native stage-one Hamiltonian
`h • tilt2`, its proved Hermitian property, and the existing
`finiteSeedCompatibleStageStates`. No nontraciality or completion-failure
hypothesis is supplied.

* `tiltSeed_representedVacuumState_not_tracial`: for every vacuum stage `v`,
  the actual `representedVacuumState` on `representedCStarClosure` is not
  tracial. The proof instantiates finite-seed transport with the native matrix
  units `E01`, `E10` and `tiltHamiltonian_gibbs_matrixUnits_ne`.
* `tiltSeed_algebraic_product_readback_ne`: the normalized density-weighted
  algebraic colimit functional distinguishes the stage injections of
  `E01 * E10` and `E10 * E01`. The proof uses the existing seed Gibbs readback.

The candidate reuses the native Matrix-to-CStarMatrix transport through the
transport owner; it introduces no carrier, state construction, or assumed
positivity instance. Dependent matrix-stage instance families are explicit;
the represented closure uses the exact public spectral-order instances of
`FilteredGNSVacuumState`, matching frozen transport v2.

This is a concrete nontraciality consumer, not a general classification of
KMS states or a claim about analytic dynamics. At `β * h = 0` no conclusion
is asserted. The Hamiltonian is seeded at stage one, not propagated from the
scalar stage zero.

Status: source-only, uncompiled; AA and serialized kernel QA remain required.
Transport v2 remains separately frozen and unchanged. No live owners were
edited and no build or test was run for this freeze.
