# Matrix-weighted Gaussian block-spin contribution

This directory stages an upstream contribution for
[`MathePhysics/4D_Wilson_Loop_RG`](https://github.com/MathePhysics/4D_Wilson_Loop_RG)
at commit `9a4492cc6bdf3338379123a085af59dfd8018a9c`. The target package is
`LEAN/Libraries/GaussianBlockSpin`, with Lean **4.34.0-rc2** and Mathlib
**8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a**. This repository's own dependency
pins are unchanged.

The supplied comparison requested a first contribution covering matrix-valued
coarse precision, positive covariance identities, exact minimization, actual
normalized Gaussian composition, scalar readback, and a noncommuting example.
The source implementation is in `overlay/GaussianBlockSpin/MatrixWeighted/`.
The full mathematical contract, volume conventions, and attribution are in
[`overlay/MATRIX_WEIGHTED.md`](overlay/MATRIX_WEIGHTED.md).

## Status and publication boundary

The eight owners have independent mathematical/source review. Native
elaboration is checked by the dedicated **Matrix Gaussian port at the Wilson
upstream pins** workflow, with exact source fingerprints and a complete
owned-declaration axiom audit. Source review alone is not a compilation result.
Read the successful run's `result.json` for the exact certified revision.

This is a contribution-staging PR in `nickgou-nuke/info-geometry-lean`.
The available GitHub connection has read access to the upstream repository,
has no fork-creation operation, and has no upstream push permission. An actual
upstream PR still requires a writable fork. The generated patch is ready to
apply to that fork; publication here does not claim upstream submission.
The committed [`upstream.patch`](upstream.patch) is checked for byte-for-byte
agreement with the overlay during preparation.

The earlier operator owners are adapted from this repository at
`fe24e350b08fdea04f74c0748ef9fd9417c47529`. The new integral proofs reuse the
upstream `GaussianIntegral` and `Kernel` interfaces. The selected scope does
not include a native Markov-kernel adapter, GNS completion, UV-uniform bounds,
or interacting Wilson-loop limits.

## Reproduce on the actual upstream source

From this repository, with Git and Python available:

```sh
python3 -B contributions/wilson-gaussian/check.py \
  --prepare-only --workdir /tmp/wilson-upstream \
  --patch /tmp/wilson-evidence/upstream.patch
```

This creates an independent sparse checkout at the exact upstream commit,
adds the eight modules and their umbrella, preserves Apache attribution,
and appends one import and a documentation link to the upstream package.
It refuses a nonempty destination and does not overwrite upstream owner files.

After installing the toolchain from that package's `lean-toolchain`:

```sh
python3 -B contributions/wilson-gaussian/check.py \
  --workdir /tmp/wilson-upstream --output /tmp/wilson-evidence
```

The script serializes compiler commands using the maintained shared lock.
Because upstream commits no `lake-manifest.json` for this package, the first
run resolves its already-pinned requirement. It then checks every resolved
dependency against the pinned Mathlib manifest and records their exact heads.
Existing manifests are not refreshed. It builds the selected umbrella,
freshly elaborates all eight owners with warnings as errors, and audits every
owned declaration against `propext`, `Classical.choice`, and `Quot.sound`.

The evidence includes command logs, the resolved manifest, all target-package
source fingerprints, and the upstream patch. This scoped check does not
certify the whole Wilson repository or this repository's root integration gate.
