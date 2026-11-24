# Real matrix Gaussian kernel verification

This profile compiles the contributed native owners with the repository's
unchanged Lean 4.34.1 / Mathlib d13f23b7 pins, freshly elaborates the selected
owners with warnings as errors, and audits every owned declaration.

The default and complete selection is `GaussianNoiseComposition`,
`MatrixGaussianKernel`, `MatrixGaussianComposition`, and
`MatrixGaussianExamples`, all under `InfoGeometry.OperatorAlgebra`.

Put the pinned runtime on PATH. Existing exact-pinned dependencies may be
reused through the maintained Lake package-overrides mechanism:

```bash
python3 verification/matrix-gaussian-kernels/check.py \
  --work /absolute/path/outside/repository/matrix-gaussian-build \
  --package-root /absolute/path/to/exact-pinned/packages \
  --phase final
```

Use `--phase build` during repair. `--no-wait` fails immediately when the
maintained shared compiler lock is occupied; it never bypasses the lock.
The work directory must be empty or already belong to this source checkout.
The runner checks dependency pins/cleanliness, source and control hashes,
runtime versions, and the repository commit before accepting its receipt.
It captures executable-control hashes before importing helpers or waiting
for the lock, checks them on acquiring the lock, and checks them at completion.

For a fresh hosted checkout, hydrate the existing pinned dependencies with
the maintained route:

```bash
python3 verification/real-matrix-split/check.py exe cache get
```

The profile's historical source is the reviewed exact-source Zorn verifier;
it retains the same shared-lock and acceptance machinery with a separate
project marker and owner selection. It does not modify dependency pins,
replace root-package checks, or certify the external GaussianBlockSpin
package's different Lean 4.34.0-rc2 / Mathlib 8d52ea9a environment.

The verbatim intake is `intake-20261124.txt`. The mathematical scope and
external integration boundary are recorded in
`docs/MATRIX_GAUSSIAN_KERNEL_CONTRACT_20261124.md`.
