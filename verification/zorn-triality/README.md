# Native real Zorn triality and Clifford verification

From an independent checkout with the pinned runtime and package sources:

```bash
python3 verification/zorn-triality/check.py \
  --repo "$PWD" --output /absolute/new/report-directory
```

The report directory must be new and outside `lean/` and `src/`. Put the
pinned runtime on `PATH`. Every Lake command goes through the maintained
`verification/real-matrix-split/check.py` shared-lock wrapper. The selected
package uses the repository's actual `lean/` sources and pinned dependencies.
This entry point reuses `real-dirac-spin-nambu/check.py` without changing its
original defaults, source checks, or acceptance gates.

## Selected scope

The four explicit build targets and fresh warning-as-error file checks are:

- `Canonical.ZornInfinitesimalTriality`: the existing norm's unhalved polar
  form, native vector and chiral spin bivectors, gamma CAR, the exact related
  triple identity, and vector-action skew-adjointness.
- `Canonical.ZornTrialityMatrixDerivations`: the transported quaternion and
  hyperbolic axes, rotation and boost bivector combinations, their equality
  with native trace-zero matrix derivations, both diagonal spin actions, and
  the indicated axis/square witnesses. Exact coefficient-matrix and native
  endomorphism witnesses show that the rotation and boost do not commute.
- `Canonical.ZornCliffordFaithful`: an explicit norm isometry through the
  existing Witt and neutral spaces, the existing split Clifford matrix
  classification, simplicity and injectivity of the actual doubled real
  representation, and its upgrade to an algebra equivalence.
- `Lie.SplitOctonionCliffordNoninjective`: the unchanged dimension obstruction
  for the full seven-generator Clifford algebra acting on one Zorn copy.

The faithful sixteen-dimensional action of real Cl(4,4) and the nonfaithful
eight-dimensional action of full real Cl(4,3) are different representations.
The verifier checks both owners explicitly. It does not infer group
classification, exponentiated actions, or physical dynamics. The rotation
and boost square readouts are on the specified axis, not the entire module.

All explicit public declaration heads in the four owners and eighteen named
upstream declarations enter a freshly generated `#print axioms` probe. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed. The expected count
is computed from the selected source: the new owners have 41 theorems and
11 definitions, the unchanged noninjectivity owner has four heads, and the
eighteen reused declarations give 74 expected records. An inventory is not
an observed axiom audit; private proof helpers are covered through consumers.

The runner checks forbidden constructs, root/focused pins, the pinned Lean
version, explicit builds, fresh elaboration, axiom records, and unchanged
source/control hashes. It does not install dependencies or update pins.
Exit codes are `0` passed, `1` failed, `2` blocked, and `130` interrupted.
Static gates, independent mathematical review, and kernel validation are
reported separately. No focused check certifies every tracked repository
file. See `handover/injections/zorn-triality-20261124.md` for the frozen intake,
precise conventions, provenance, and actual validation status.

## GitHub Actions

`.github/workflows/zorn-triality.yml` runs this same entry point. Its public
Git checkout fetches the exact event revision without traversing the
repository's existing external gitlinks, then verifies the checked SHA. The
workflow records the commit and tree, installs the exact repository toolchain,
hydrates pinned artifacts through the shared-lock wrapper, checks package
revisions, URLs, clean sources, and unchanged manifests, and uploads the
complete validation directory even on failure or blockage.

The dependency-cache key is shared with the parent Zorn/Witt workflow because
the frozen toolchain and package closure are identical. Pull requests do not
write this cache; the existing save policy permits only a manual workflow
dispatch after the pin-integrity step succeeds. Neither a cache hit nor an
unrelated green workflow establishes acceptance of the selected Lean owners.
