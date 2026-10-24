# Drazin / Moore-Penrose partition implementation

Source: `Pasted text(20261023-003553).txt`.
Base: main `31d1d9baeb4138976a8ec06535d83993c2c213f3`.
The base already contains `docs/DRAZIN_MP_PARTITION_AUDIT.md`; its corrected
contract is retained, not overwritten. No dependency on unmerged attention
PRs is introduced. No inverse predicate is redefined.

## Owners and mathematical scope

The canonical Drazin owner supplies `IsDrazinInverse`, `projection`,
`complementaryProjection`, `core`, `nilpotent`, and the Fitting identities.
The singular Moore-Penrose owner supplies the four Penrose equations.
Mathlib `IsStarProjection` supplies native self-adjoint idempotent calculus.

New modules:

- `Canonical.DrazinRegularization`: explicit native unit C+F with inverse D+F
  at arbitrary witness exponent; inverse/support identities; exponent-zero
  case; constant nonzero scalar transport and invariant spectral projectors.
- `Singular.MoorePenroseSectors`: four Boolean support sectors, their universal
  sum, full multiplication table under commutation, native star projections,
  exact boundary-square commutation obstruction, Jordan identity, and
  compatibility-qualified refinement by a third star projection.
- `Canonical.DrazinMoorePenrosePartition`: DMP and dual products with derived
  outer-inverse laws, cyclic-trace identity, MP/scalar transport and sector
  invariance. These products are not assumed to be new Penrose inverses.
- `Singular.MoorePenrosePowerShells`: MP supports of each actual power, nested
  support laws, range and kernel-growth shells, native star projections,
  orthogonality for ordered distinct levels, and ambient telescoping sums.
- `Canonical.InversePartitionExamples`: full 3-by-3 shift identities; a
  4-by-4 nilpotent counterexample with noncommuting MP supports and a
  nonidempotent squared commutator; an oblique Drazin projector example.
- `Canonical.DrazinMoorePenrosePartitionAll`: small production import surface.

## Distinctions preserved from the corrected contract

An invertible core is not necessarily volume preserving. The witness exponent
is not asserted minimal. At exponent zero the nilpotent part vanishes, but
its zeroth ambient power is one. Existing positive-power nilpotency belongs
to `Canonical.DrazinCoreFlow` and is not redeclared here.

For supports p=XM and q=MX, the four summands always sum to one, but their
projection multiplication law requires pq=qp. The attachment explicitly
supplies commutation for its Jordan-Lie theorem. This implementation retains
that assumption and strengthens the boundary identity to an equivalence:

    [p(1-q)+(1-p)q] - (p-q)^2 = qp-pq.
    p(1-q)+(1-p)q = (p-q)^2 iff pq=qp.

The MP commutator XM-MX is self-adjoint. Zero trace alone is not a discrete
Stokes theorem. Constant scalar homogeneity is not local Weyl geometry.

The range-shell filtration uses im(A^m); kernel-growth shells use ker(A^m).
They are not interchangeable. Both sums are the identity on the chosen
ambient nilpotent carrier. An oblique Drazin complement cannot silently be
substituted for that identity; restriction of the carrier is separate.
Powers of MP inverses are not assumed to be MP inverses of powers.

A self-adjoint coarse projector commuting with both fine supports is a
sufficient compatibility hypothesis for the native star-projection refinement
proved here. An arbitrary Drazin projector need not meet this condition.
This change does not identify the zero spectral sector of I-P with all
transient Markov modes or change any attention backward pass.

## Actual verification

Verified Lean source commit: `c247857313d4e8e005c79d98ab5ce7caa50284d2`.
Successful scoped workflow:
https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/39884496772
Job: `120189379622`. The later documentation commit does not change Lean source.

Lean: `leanprover/lean4:v4.34.1`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (unchanged repository pin).

All six new Lean modules compiled, including the production umbrella and
matrix examples. Their six existing repository dependencies were compiled
from full unchanged owner sources: FiniteSpinAlgebra, DAG.Basic,
Meta.Architecture, Singular.MoorePenrose, Singular.Drazin, Canonical.Drazin.

There are 60 new proved declarations (47 theorems and 13 lemmas), plus
11 definitions. All 71 were checked with `#print axioms`. Every footprint is
a subset of `[propext, Classical.choice, Quot.sound]`; some are empty or
smaller. The workflow checks audit count completeness and the allowed set.
The new sources contain no `sorry`, `admit`, custom axioms, `unsafe`, or
`native_decide`. Compilation is the evidence, not the input draft's assertion.

Workflow artifact: `DrazinMoorePenrosePartitions`, ID `12472286861`, contains
the exact new sources, compile output, full axiom audit and machine-readable
status. Its downloaded ZIP SHA-256 was independently checked against GitHub:
`3defa138fed33889257c2efd649ecca6f1641afc519b47120fa7eae8ff234162`.

Nonfatal warnings remain for unused simp arguments and section assumptions,
plus pre-existing dependency deprecations and sandbox/Grassmann.jl cleanup.
The separate unchanged repository gates are not all green: the same checked
commit has two failed workflow runs, including Sorry Gate run 39884496767.
Their failures are not diagnosed or repaired here. This is not a full-repository
acceptance check, and no claim that all repository CI passed is made.

No dependency pins were changed, no existing owner source was rewritten, and
no build caches were deleted. The build is sequential under the shared lock.

Use in a full checkout:

```lean
import InfoGeometry.Canonical.DrazinMoorePenrosePartitionAll
```

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.DrazinMoorePenrosePartitionAll \
  InfoGeometry.Canonical.InversePartitionExamples
```
