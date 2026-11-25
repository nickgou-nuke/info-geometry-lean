# Matrix-weighted real Gaussian integration

## Contract

For arbitrary finite index types, real Euclidean spaces, positive definite real
matrices `A` and `R`, and an arbitrary rectangular observation matrix `Q`, define
the normalized matrix-weighted Gaussian block kernel. Prove normalization in
the coarse variable, the exact determinant-normalized integral against a fine
Gaussian, scalar specialization to the existing `blockKernel`, and normalized
composition with arbitrary positive definite noise precision matrices.

Reuse the prepared native matrix Schur-complement and square-completion owners
and the upstream general positive-definite Gaussian integral. Prove the Schur
determinant identity needed by convolution rather than taking it as an input.

## Scope

Real finite-dimensional Euclidean Lebesgue integration, without commutation,
coisometry, rank, or scalar-noise restrictions. This does not construct a
`ProbabilityTheory.Kernel`, prove a model-specific gauge coercivity estimate,
or establish a Wilson-loop continuum limit.

## Provenance and validation

New integration extension of the previously prepared Gaussian contribution.
The source conventions were audited against upstream commit
`9a4492cc6bdf3338379123a085af59dfd8018a9c`.

All **11 public theorems** in `WeightedKernel.lean` and
`WeightedKernelConvolution.lean` passed the exact destination build and fresh
axiom audit as part of the combined Gaussian contribution:

- Lean: **4.34.0-rc2**.
- Mathlib: **`8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`**.
- Preparation commit: **`0d848bd531f595d8cac0e06b13dad2e48fca8132`**.
- [Workflow run 45458690593, job 138675000523](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45458690593/job/138675000523).
- Focused audit-target build with warnings treated as errors: **passed**.
- Separate fresh combined axiom audit: **54 reports passed**, including all
  11 new integration declarations. Each report contains only `propext`,
  `Classical.choice`, and `Quot.sound`.

The parent retrieved artifact **14952650617** and matched all nine combined
Lean source hashes to the checked sources. The two integration owner hashes
are:

| Owner | SHA256 |
| --- | --- |
| `WeightedKernel.lean` | `9deb8cbbe86c20847b1aaac49d582b18a87361e0251ff1c7bc4528e264e676e0` |
| `WeightedKernelConvolution.lean` | `2da94c02dcb9a9ff4594658e83a1e961224c0eb4517f1f4b35087e7e34608477` |

[Build logs, fresh axiom output, dependency revisions, and source inventory](../../validation/evidence/exact-gaussian-0d848bd/)
record the validation. The source statements and normalization were also
reviewed independently by the parent and Gaussian specialization worker.
The only initial destination diagnostics in these two owners were two
proof-local `letI` style warnings; replacing them by `let` left the theorem
statements unchanged and the final destination run passed.

This is a focused check of the Gaussian contribution and its dependency
closure. It does not assert a whole-repository build or discharge the physical
and analytic obligations excluded in the scope above.
