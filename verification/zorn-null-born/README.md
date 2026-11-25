# Native Zorn null kernels, Witt operators, and oriented volume

From an independent checkout with the pinned Lean runtime and package sources:

```bash
python3 verification/zorn-null-born/check.py \
  --repo "$PWD" --output /absolute/new/report-directory
```

The output directory must be new and outside `lean/` and `src/`. The entry point
selects exact owners through the existing `real-dirac-spin-nambu/check.py`
verifier; every compiler command uses the maintained
`verification/real-matrix-split/check.py` shared-lock wrapper. It preserves the
existing verifier's checks, defaults, pins, and axiom acceptance policy.

## Scope

- `Lie.CanonicalZornNullKernel`: actual regular-operator trace and polarized
  contractions, the conjugate range/left-kernel equality for every nonzero
  null Zorn element, and its four-dimensional kernel.
- `Canonical.ZornWittBorn`: an explicit norm isometry, transport of existing
  normalized Witt generators through the existing real Dirac representation,
  and the four-negative-generator product and its exchange identities.
- `Canonical.ZornVolumeAction`: exact Born reflection on each Zorn summand
  and the oriented volume action `(s,t) ↦ (s,-t)`.
- `Canonical.ZornCliffordFaithful`: the actual full real Cl(4,4) algebra
  equivalence for the doubled sixteen-dimensional representation.
- `Lie.SplitOctonionCliffordNoninjective`: the existing dimension obstruction
  for the full Cl(4,3) algebra acting on one eight-dimensional Zorn copy.

The checker inventories all explicit public heads of these owners and twenty
named upstream declarations, generates a fresh `#print axioms` probe, and
requires each record. Private proof helpers are covered by their public
consumers. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
An inventory count is separate from the count of actually observed records.
The reviewed source inventory is 60 owner heads plus 20 distinct reused
declarations, giving 80 expected records. The three new owners contribute
36 theorems and five definitions; the other 19 heads belong to the two
existing representation-boundary owners.

Validation includes forbidden-construct and pin checks, the pinned runtime
version, explicit builds, fresh warning-as-error elaboration, the axiom probe,
and unchanged source/control hashes. Exit codes are 0 passed, 1 failed,
2 blocked, and 130 interrupted. Static gates, mathematical source review,
and kernel acceptance are recorded separately. No focused run certifies every
tracked repository file.

The GitHub Actions workflow records the exact event revision and tree, uses
the established public Git checkout, restores and verifies pinned dependency
artifacts, runs this entry point, and uploads evidence on every outcome. It
shares the frozen dependency cache with the parent Zorn workflows; pull
requests do not save that cache.

See `handover/injections/zorn-null-born-20261124.md` for the frozen intake,
counterexamples to the proposed multiplication table, normalization,
provenance, and actual validation status.
