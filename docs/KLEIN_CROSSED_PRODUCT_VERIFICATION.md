# Klein formalization: verification protocol and execution record

## Acceptance and published source

The authoritative current native result is the **Klein crossed product
(scoped kernel)** workflow for the exact head of
[upstream draft PR #371](https://github.com/nickgou-nuke/info-geometry-lean/pull/371).
A successful check requires compilation of the complete selected source
closure, the native declaration axiom audit, and zero warnings in each of
the four selected owners. Source review, text scans, and publication as a
draft do not independently establish kernel acceptance.

The initial published commit is
`7f1093f99c0b97bb3bc55a55f7b181d18bbbc5a3`, whose tree
`074ac3dc28970c1a6de4711f76823ac871f5d7a2` was read back from upstream and
matched the reviewed local tree. Its first workflow run is recorded below.
Subsequent heads must obtain their own native check; do not treat the older
failed result as either a proof of a repaired source or a new failure of it.

The work branch is `codex/klein-crossed-product-20261116`, based on
`08c34e03f610b452e03422037949196dc7d92d6d`. The earlier split-spinor PR #363
is separate. See [the contract](KLEIN_CROSSED_PRODUCT_CONTRACT.md) for exact
carriers, hypotheses, and open mathematical boundaries, and
[the review](KLEIN_CROSSED_PRODUCT_REVIEW.md) for independent source review.

## Source scope

| Mathematical owner | New theorem declarations | New definitions |
| --- | ---: | ---: |
| `Algebra/SkewPolynomialFactorization.lean` | 5, including one private helper | 0 |
| `Algebra/QuadraticCrossedProduct.lean` | 22 | 9 |
| `Algebra/CARTwoSidedIdeal.lean` | 8 | 1 |
| Existing `OperatorAlgebra/Z2ProjectorWeights.lean` | 4 | 0 |
| **Total** | **39: 38 public and one private** | **10** |

These are source-declaration counts. The native audit also covers generated
owned declarations and the ten pre-existing theorems and three definitions
in the changed projector owner. `InfoGeometry.All` imports the three new
modules. The selected four owners have an exact ten-module repository source
closure; the workflow does not compile the full aggregator.

## Source checks and independent review

The four owners passed strict placeholder checks, the semantic vacuity gate
at blocking level `error`, and the strict OpenGauss screener. The semantic
scan has two reviewed warning-level findings: `matrix_trace` and the unchanged
`AlgHom.map_projectorWeight`. These are meaningful computational statements,
not vacuous conclusions. Their proofs were not padded to avoid lexical flags.
The independent mathematical and pinned-API reviews cover the original
candidates and all compiler repairs.

The installed staged proof gate ran successfully for the recovered source
checkpoint and subsequent commits. `git diff --check` also passed. Current
source hashes, exact arguments, and exit codes are retained in the local
verification evidence; these checks are distinct from native compilation.

The CI workflow passed independent source review, YAML parsing, shell syntax
checking, and parsing of all embedded Python. Its reviewed SHA-256 is
`20992d957874409297718d5c1330d2bcc1beab32ec3f43960153aa2d3d5dc3f2`.

## Native execution history

### Initial local pass, 2026-11-16

Seven of ten modules compiled. The CAR owner had zero warnings. Three selected
owners needed proof-body repairs: explicit skew product-to-monomial rewriting,
explicit involutivity/map-zero simplification in the matrix calculations, and
`sub_eq_zero` for the projector equivalences. Their statements, assumptions,
carriers, and product order were unchanged. The axiom audit was not reached.

The following repaired-source attempt could not obtain the shared lock and
returned `Shared lock unavailable after 600 seconds` with an empty module
result list. Its old compiler logs are historical, not fresh diagnostics on
the repaired bodies.

### Recovery and first upstream pass, 2026-11-17

The saved source tree was restored exactly as
`62ae67e7a9e3ffed9477d49883cdfb91e6f163d7`, then the focused CI workflow and
its review were added. The pinned compiler archive checksum was verified
before extraction, and the independent Mathlib checkout matched the exact pin.
Two local recovery attempts timed out after 600 seconds each while acquiring
the shared lock. Neither attempt ran a cache or compiler command; no holder
was terminated and the lock was not bypassed.

[Upstream run 44045834678](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44045834678)
successfully recovered the pinned dependencies and compiled nine of ten
modules. The quadratic matrix, CAR ideal, and projector owners all compiled
with zero warnings. Seven warnings occurred in unchanged dependencies:
five in `SplitCliffordAlgebras` and two in `CPTComplexStructure`.

The skew coefficient proof still failed: its restricted simplifier left
`(if True then φ u - u else 0) = 0`, and `if_pos` was deprecated. The final
minimal repair keeps the explicit monomial rewrite and replaces that step
with `simpa [coeff_monomial] using hcoeff`. A different reviewer checked it
against the pinned source. That run did not reach the declaration audit;
acceptance of the repair is determined by the subsequent exact-head workflow.
The complete first-run source snapshots, report, and logs are retained in its
[verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/44045834678/artifacts/14312065892).

## Reproduce the native check

Use Lean `leanprover/lean4:v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The official Linux compiler
archive SHA-256 is
`47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
No dependency pin or maintained checker was changed.

From an independent repository checkout, with the pinned runtime and Mathlib
initialized according to the shared-lock/cache policy:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/ecf0f7649d13/pinned-mathlib \
  --lean /workspace/scratch/ecf0f7649d13/lean-runtime/bin/lean \
  --output /workspace/scratch/ecf0f7649d13/verification-klein-20261117 \
  --target InfoGeometry.Algebra.SkewPolynomialFactorization \
  --target InfoGeometry.Algebra.QuadraticCrossedProduct \
  --target InfoGeometry.Algebra.CARTwoSidedIdeal \
  --target InfoGeometry.OperatorAlgebra.Z2ProjectorWeights
```

Substitute only runtime/output paths for another machine. Do not add
`--skip-audit`. The native audit checks every declaration owned by each
selected target, including private/generated declarations, against the
allowed foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.
It rejects unsafe or partial declarations and reconciles the ownership counts.

The focused CI workflow fetches the exact PR head, checks the unchanged pins,
verifies fresh compiler downloads, and restores only pinned dependencies.
Cache hydration and compilation use the original shared lock, with its
file descriptor inherited by relevant subprocesses. Each run and attempt has
fresh repository output. A report guard additionally requires the exact head,
target list, successful native audit, and zero warnings in all selected owners.
Reports, logs, source snapshots, and audit output are uploaded on completion.

## Separate integration boundaries

A scoped native success does not certify the full `InfoGeometry.All` aggregator
or root Lake workspace. The fresh checkout lacks the declared path packages
`external_refs/homotopy-hypothesis-lean4` and `external_refs/atlas-lean`.
An earlier split-spinor pre-push attempt failed on the first of these; that
historical execution is not a new root gate run for this patch. No missing
source URL or revision is invented, and the existing root hooks and quality
workflows remain unchanged.

The first PR style job also failed before running the Lean linter because
both `lean/Docs` and `lean/docs` exist. Both directory trees are already
present at the base revision and unchanged by this patch. This repository
case-collision failure is separate from the selected-owner compiler results.
The PR remains a draft while root integration is unresolved.
