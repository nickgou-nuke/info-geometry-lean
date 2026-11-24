# Native Zorn regular-operator verification

From an independent checkout with the pinned runtime and package sources:

```bash
python3 verification/zorn-witt-regular/check.py \
  --repo "$PWD" --output /absolute/new/report-directory
```

The report directory must be new and outside `lean/` and `src/`. Put the
pinned runtime on `PATH`. Every Lake command goes through the existing
`verification/real-matrix-split/check.py` shared-lock wrapper. The selected
package uses the repository's actual `lean/` sources and pinned dependencies.
The parameterized implementation in `real-dirac-spin-nambu/check.py` is reused
without changing its original defaults or gate semantics.

## Selected scope

The four explicit build targets and fresh warning-as-error file checks are:

- `Lie.CanonicalZornRegularNorm`: canonical left-operator alternativity,
  conjugate contraction, explicit inverses, unit equivalence, and determinant
  singularity in an arbitrary genuine eight-element basis.
- `Lie.CanonicalZornWittRegularBridge`: the composition of existing coordinate
  equivalences, native norm/pairing compatibility, chiral square laws, the full
  mixed anticommutator, vector–covector incidence consequences, a noncommuting
  pair, and the exact negative-sign chiral associator defect.
- `Lie.CanonicalZornRegularExactDet`: the actual Cartesian matrix of the
  existing operator, and its determinant `N(Z)^4` in any eight-element basis.
- `Lie.SplitOctonionCliffordNoninjective`: the unchanged existing dimension
  obstruction to faithfulness of the full seven-generator Clifford action.

All explicit public declaration heads in these owners and ten named upstream
declarations enter a freshly generated `#print axioms` probe. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Private helpers are covered
through their public consumers. The exact expected count is computed from
the selected source; an inventory is not an observed axiom audit. The reviewed
snapshot has 29 owner heads (9 + 12 + 4 + 4), giving 39 expected axiom records.
The two additional determinant-owner theorems witness noncommutativity of
actual upper/lower chiral left-action matrices and of actual four-dimensional
upper blocks in the same Cartesian representation.

The verifier checks forbidden proof constructs, root/focused pins, the pinned
Lean version, explicit builds, fresh elaboration, axiom records, and unchanged
source/control hashes. It does not install dependencies or update pins.
Exit codes are `0` passed, `1` failed, `2` blocked, and `130` interrupted.

This focused check is separate from static/source gates, independent semantic
review, and root integration. A busy shared lock or absent compiler output
does not establish theorem acceptance. The exact determinant value
`det(L_Z) = N(Z)^4` is checked separately from the zero-set proof: incidence
and the inverse criterion do not depend on the finite determinant expansion.
See `handover/injections/zorn-witt-regular-20261124.md` for the frozen intake,
claim corrections, and actual final validation status.

## GitHub Actions

`.github/workflows/zorn-witt-regular.yml` runs this same checker for the
selected source and verification paths. It records the checked commit/tree,
installs the exact repository toolchain, hydrates the pinned package artifacts
through the maintained shared-lock wrapper, and checks package revisions,
URLs, clean sources, and unchanged manifests before building. The complete
checker output directory is uploaded, including failed or blocked reports.
The workflow does not turn unrelated green jobs into acceptance of this packet.
