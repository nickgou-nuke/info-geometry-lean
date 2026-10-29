# Chiral dissipator and algebraic direct-limit contract

## Intake and scope

Source: user request, 2026-10-29. Extract pure noncommutative mathematics from
the proposed two-sheet/chiral-parity framework, progressing from finite full
matrix algebras through inductive colimits into infinite operator rings.
Complete native Lean proofs only; no scalar, diagonal, or commuting substitutes.
Physical mass-gap and spontaneous-symmetry-breaking interpretations are intake,
not theorem conclusions.

## Exact carriers and owners

`SymmetricDissipator.dissipator` is the native `Module.End R A`
`-(ad u * ad v + ad v * ad u)` on an associative `R`-algebra. Its evaluated
formula is `2 • (u*x*v + v*x*u) - ((u*v+v*u)*x + x*(u*v+v*u))`.
The matrix specialization is proved equal to the existing corrected
`Core.SquareZeroSandwich.symmDissipator`, rather than replacing that owner.

The first direct-limit specialization uses `Cl11TensorTowerLimit.Limit`, the
existing full real matrix tower with dimensions `2^n`. Canonical inclusions
are injective by `DirectLimitSuperClosureLemmas.directLimitOf_injective` and
`Cl11TensorTower.matStageEmbed_injective`. Naturality, finite iterates, exact
reflection of vanishing, noncommutativity, and the existing universal lift are
proved on these actual maps.

The parity specialization uses the existing full real Boolean-word matrix ring
`PrimonColimitAlgebra.PrimonUHFAlgebra`, with the actual involutive
`PrimonSuperalgebra.globalParity`. Here the dissipator is viewed as an
integer-linear endomorphism of the same real-matrix ring; the explicit
`toColimit_dissipator` theorem connects it to the real-linear finite owner.
This does not change the coefficient field or restrict to diagonal matrices.
No new identification of the two existing colimit carriers is asserted.

Two odd charges, expressed by the existing `isFermionic` predicate, give
preservation of both existing parity sectors. The general sign-reversing
automorphism criterion does not require involutivity; the concrete owner does
prove involutivity. Generic scalar eigenspace invariance uses an algebra
automorphism. Neither assumption is hidden in a new witness structure.

## Proof dependency order

The following are logical dependencies, not temporal or physical causality:

1. Native associative inner derivations → evaluated dissipator formula.
2. Evaluated formula → agreement with finite matrix owner and ring-map naturality.
3. Naturality → finite-iterate naturality and compatible tower transport.
4. Existing injective bonds + transport → exact reflection of vanishing and
   preservation of noncommutativity in the actual direct limit.
5. Existing universal lift + transport → evaluation through every compatible ring cone.
6. Naturality + simultaneous charge sign reversal → automorphism equivariance.
7. Existing involutive global parity + equivariance → invariance of its even/odd sectors.

This records declaration dependencies; it does not introduce an artificial
`PartialOrder` on theorem names.

## Open boundary

No positive spectral lower bound, state selection, spontaneous breaking or
restoration, Yang–Mills field construction, topological completion, or
unbounded-operator extension follows from these identities. The finite-iterate
theorem is not a continuous-time semigroup theorem. Oddness of the two charges
is explicit; existence and classification of particular charges remain with
their existing owners or future constructions.

## Validation

Run `python3 scripts/quality/check-chiral-dissipator-colimit.py` with the pinned
Lean toolchain and `RUNNER_TEMP` set. It checks the complete project import
closure serially, treats new-module warnings as errors, inspects every new
declaration's axioms, rejects proof placeholders, and runs the semantic gate.
Kernel status will be recorded after the focused workflow completes.
