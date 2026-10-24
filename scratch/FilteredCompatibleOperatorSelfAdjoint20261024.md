# Self-adjointness of the native bounded completed operator

Uncompiled sandbox proposal. No live edits/builds/tests. Independent AA/QA pending.

## Grounding and reuse

Bounded source search of `Canonical/FilteredCompatibleOperator*.lean`,
`Canonical/FilteredIsometric*.lean`, and references to completedOperator with
symmetry/self-adjointness found no existing theorem with this contract.
This is a bounded search result, not a repository-wide absence certificate.

- `Canonical.FilteredCompatibleOperatorColimit`: existing
  `CompatibleOperatorFamily`, `completedOperator`, `completedOperator_stage`.
  The family already includes actual transition intertwining and a uniform
  bound; the completed operator is constructed by the native completion map.
- `Canonical.FilteredIsometricHilbertCompletion`: actual linear-isometric
  stage maps, `stageToHilbertDirectLimit_transition`, and
  `dense_iUnion_range_stageToHilbertDirectLimit`.
- Mathlib `Continuous.ext_on`, `LinearIsometry.inner_map_map`, and
  `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`.

## Three focused lemmas

In namespace `InfoGeometry.Canonical.FilteredCompatibleOperatorColimit`:

1. `completedOperator_inner_stage`: stagewise symmetry yields the required
   inner-product equality for any two stage images. Move them to a common
   upper index, use existing stage readback, then the inclusion isometry.
2. `completedOperator_isSymmetric`: extend this equality in both variables
   over the dense union of stage ranges by continuity.
3. `completedOperator_selfAdjoint`: under complete stage spaces, stagewise
   `IsSelfAdjoint` gives `IsSelfAdjoint (completedOperator E sys T)`.

The first two statements require no complete stages. The final assumption
`forall i, CompleteSpace (E i)` supports the native Hilbert adjoint on stage
continuous endomorphisms. The target completion is already complete.

No new carrier, family structure, operator definition, or hPair field is added.
No completed symmetry/self-adjointness premise is assumed.

## Scope boundary

This is the bounded completion replacement for the inappropriate demand that
every completed vector have an exact finite-stage representative. It neither
constructs a concrete Dirac tower nor proves a proposed tower intertwines or
has a uniform bound. In particular it does not repair the incompatible
`ConcreteCliffordDiracTower.Dfinite n = n * id` cutoff model, and does not make
an unbounded Dirac/spectral statement.

## Verification handoff

Check instance availability for the completed Hilbert space, common-upper
rewrites, continuity inference on inner products, and native symmetry coercions.
Author performed source inspection only; no kernel/axiom-clean claim is made.
