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
`[kernel_verified]` — focused run
[40855707974](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40855707974),
job `123386012770`, passed all 20 modules in the complete import closure and
the exact-set audit of 21 new declarations (20 theorems and one definition).

- Checked source: `6bef22fc2fe6767f99f11ea3c7750cb0082202d0`.
- Checked merge: `55b604895173832d21560e4f576345b2bc8ae715`.
- Base: `87bfa4567046db6f475a9df2903bd4060dc773ca`.
- Lean 4.34.1, compiler `5045d0056413266e57c625dcd7c365b10e377c52`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur in the axiom audit.
- Zero Lean warnings in new modules; 18 existing imported-owner warnings.
- Semantic gate: two warning-only helper findings, `dissipator_one` and
  `map_dissipator`; no errors. The first proves identity annihilation, and the
  second is the naturality lemma consumed by the colimit and parity proofs.
  Neither is an empty proposition or a supplied proof field.
- Independent semantic audit passed for the exact carrier/hypothesis scope.

Source SHA256 values:

| File | SHA256 |
| --- | --- |
| `OperatorAlgebra/SymmetricDissipator.lean` | `a10d50a765107381df8f256144b9be745f8fc4826468bc65be1db30fcf9b43d0` |
| `Canonical/SymmetricDissipatorColimit.lean` | `986b70cff04dda0f52e22d81956fda9235eef1930c7571dd73a3f1c8950ac873` |
| `Canonical/SymmetricDissipatorParity.lean` | `081fb68a6df8387ed150822a40887f892564e106d57fecada5de561463b86c02` |
| `Canonical/SymmetricDissipatorAudit.lean` | `f5caee7787b4db956ca26a86cb689ccc356958e31bc83404e5db4f1e79fc1d52` |

The subsequent evidence-only documentation commit does not alter these sources,
the verification script, the workflow, or the pinned dependencies.

Repository-wide CI is a separate boundary. On source
`f954f074f1ee9e4b6342cd82c19139fe4a94b51f`, the unchanged wider checks reported:

- Style run `40854574169`: existing case collision between
  `Physics/PellisFineStructure.lean` and `Physics/PellisfineStructure.lean`.
- Sorry Gate run `40854574113`: repository-wide audit reports 91 debt files
  and 878 findings; these new sources contain no placeholders.
- CI run `40854574134`: local-package validation fails; subsequent smoke
  summary reports missing `external_refs/atlas-lean`.
- Reviewed PR Integration run `40854574082`: checkout cannot clone the
  existing local-only `/home/goutev/repos/pure_math_lib` submodule URL.

These results do not constitute a green repository-wide build.
