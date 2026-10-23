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
projection multiplication law requires pq=qp. In fact

    [p(1-q)+(1-p)q] - (p-q)^2 = qp-pq.

The MP commutator XM-MX is self-adjoint. Zero trace alone is not a discrete
Stokes theorem. Constant scalar homogeneity is not local Weyl geometry.

The range-shell filtration uses im(A^m); kernel-growth shells use ker(A^m).
They are not interchangeable. Both sums are the identity on the chosen
ambient nilpotent carrier. An oblique Drazin complement cannot silently be
substituted for that identity; restriction of the carrier is separate.
Powers of MP inverses are not assumed to be MP inverses of powers.

The orthogonal refinement needs a self-adjoint coarse projector commuting
with both fine supports. An arbitrary Drazin projector need not meet this
condition. This change does not identify the zero spectral sector of I-P
with all transient Markov modes or change any attention backward pass.

## Verification boundary

Sources are candidates until the scoped pinned workflow succeeds. It checks
full unchanged owner dependencies, the new modules and the small umbrella,
and inspects the actual axiom dependencies of each new declaration. Exact
source commit and results are to be recorded after a successful run.
No full-repository acceptance is implied. The workflow does not delete caches,
change dependency pins, or repair unrelated owner files.
