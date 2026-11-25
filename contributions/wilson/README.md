# Wilson RG contribution candidates

Three independent contributions prepared for
[`MathePhysics/4D_Wilson_Loop_RG`](https://github.com/MathePhysics/4D_Wilson_Loop_RG),
at upstream commit `9a4492cc6bdf3338379123a085af59dfd8018a9c`.

This branch hosts the source proposals and isolated destination-pin verification.
It is not an upstream pull request and does not assert a completed continuum
limit proof. Read each contribution's theorem contract for its explicit inputs.

All three contributions have passed preliminary Lean 4.34.1 compilation with
zero warnings and complete fresh axiom inventories. See
[validation status](validation/STATUS.md) for the evidence and the distinct
destination-pin and publication gates. The [publishing directory](publishing/)
contains independent Git patches and prepared pull-request descriptions.

| Candidate | Destination | Contract |
| --- | --- | --- |
| `gaussian/` | `LEAN/Libraries/GaussianBlockSpin` | Weighted precision/covariance, ordered two-stage elimination, and an adapter consuming the existing Gaussian integral with its determinant normalization. |
| `cutoff/` | `LEAN/CoreLean` | Relative normalized cutoff comparison, weighted positive-cone recursion estimates, power-log summability, and conditional convergence with a quantitative tail. |
| `gram/` | `LEAN/CoreLean` | Complex finite Gram quotients, zero-extension maps, native module direct limit, dense Hilbert completion, and passage of kernel positivity through pointwise limits. |

The Gaussian matrix owners are adapted from InfoGeometry at
`5e6396f87f8d4d0959c88896975b1aaaf3979009`; the kernel construction also adapts
Mathlib's scalar pre-inner-product pattern. Apache 2.0 notices are included.

## Validation

The workflow `.github/workflows/wilson-upstream-validation.yml` overlays each
candidate into a separate checkout of the pinned upstream revision. It leaves
upstream's toolchain and dependency configuration unchanged:

- GaussianBlockSpin: Lean `4.34.0-rc2`, Mathlib
  `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`.
- CoreLean: Lean `4.36.0`, Mathlib
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

The checks compile the focused dependency closure with warnings treated as
errors, produce a fresh `#print axioms` transcript, require every public
theorem in the explicit inventory, reject unexpected foundational assumptions,
and retain source hashes and the resolved manifest in downloadable evidence.
Each workflow result applies only to its checked commit. A workflow definition
or source review alone is not compiler evidence.

The physical RG estimates, positive partition functions, reflection positivity,
and pointwise cutoff convergence remain explicit hypotheses at the relevant
interfaces. Algebraic direct limits of exactly compatible finite test families
do not supply the analytic cutoff limit.
