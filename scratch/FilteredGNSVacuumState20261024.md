# Filtered GNS represented vacuum State: consumer contract

Status: uncompiled source candidate, pending independent AA and locked QA.
This contract is not a kernel receipt. No Lean code changes or builds accompany it.

Consumer: `scratch/FilteredGNSVacuumState20261024.lean`.
SHA-256: `9ad758cc5ddbc5d6c75fcfc8717e748f948ce49e60d2e74b1747da6e4a79066c`.
Planned import: `InfoGeometry.Canonical.FilteredGNSVacuumReadback`.
Latest repaired base candidate: `scratch/FilteredGNSVacuumReadback20261024v3.lean`,
SHA-256 `205a9acb2e4af7a2b0be418752883b4da036d8bd2937d990e34cc125db9c4326`.
The base import must resolve to the independently accepted promoted source;
this consumer neither imports scratch v3 nor establishes its acceptance.

## Existing carrier and base scope

The carrier remains
`CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure.representedCStarClosure`:
the operator-norm closure of the represented algebraic filtered colimit inside
bounded operators on the existing global GNS Hilbert completion. Its native
`CStarAlgebra` is constructed in
`lean/InfoGeometry/Canonical/FilteredGNSRepresentedCStarClosure.lean`.
No raw-colimit faithfulness or identification with this closure is asserted.

The base takes the existing directed system of ordered C-star stage algebras
and its compatible normalized positive state family. It proves global vacuum
norm one, independence of its chosen stage, and expectation recovery on every
represented stage observable. It constructs `representedVacuumFunctional` as
a continuous linear map on the closure, proving normalization and positivity
on `star a * a` by the actual Hilbert adjoint identity. These conclusions are
used as proved lemmas, not added as hypotheses in a new witness package.

## Exact spectral-order owner

Mathlib source:
`.lake/packages/mathlib/Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`,
section `SpectralOrder`, declarations:

- `CStarAlgebra.spectralOrder`: constructs `PartialOrder A` for a
  `NonUnitalCStarAlgebra A` using self-adjointness and nonnegative quasispectrum
  of differences.
- `CStarAlgebra.spectralOrderedRing`: proves `StarOrderedRing A` for precisely
  that constructed spectral order.

The consumer installs these as local instances on the existing represented
closure. No closure-order or positivity assumptions are introduced. The order
choice is encoded in the elaborated types; downstream consumers must use this
same order (or prove the necessary order identification), rather than silently
substituting an unrelated instance.

## Construction and acceptance heads

Namespace: `CStarStateColimit.Native.FilteredGNSVacuumState`.

1. `representedVacuumPositiveFunctional`: uses `PositiveLinearMap.mk₀` on the
   base continuous functional's linear map. For an arbitrary nonnegative
   closure element, `CStarAlgebra.nonneg_iff_eq_star_mul_self` supplies its square
   decomposition; the base star-square positivity theorem proves the result.
2. `representedVacuumState`: constructs the existing native `State` from this
   positive map and `representedVacuumFunctional_one`. Native `State` is owned
   by `lean/InfoGeometry/Canonical/CStarAlgebraStateColimit.lean`.
3. `representedVacuumState_stage`: for any vacuum stage i and observable stage
   j, evaluation on the represented image of `a : Stage j` equals
   `(ω.state j).functional a`.
4. `representedVacuumState_eq`: choices i and j yield equal states on the entire
   represented closure, by base vacuum equality and functional extensionality.

## Boundaries and validation debt

No new carrier, conclusion bundle, assumed positivity, or assumed normalization.
No claim of faithfulness, traciality, modular flow, KMS strip analyticity, or
new categorical completion. This is a state on the already represented closure.

Independent QA must check the promoted base, local spectral-order instance
elaboration, square-decomposition positivity, native State construction, and
both readback/independence proofs. Frozen base candidates and consumer source
remain unchanged by this documentation task.
