# Graded Clifford adjoint and cut-rank acceptance evidence

## Accepted scope

The six new Lean owners in [draft PR #355](https://github.com/nickgou-nuke/info-geometry-lean/pull/355)
passed exact-source compilation and the native all-owned declaration audit at
commit `ec36632a52860b8e710cd6b1c258a5c6f649d06e`, tree
`21b365c94f4e44fb853d342c7f7ecc04f07be35b`.

**All 44 repository-local dependency-closure modules compiled. All 197
declarations owned by the six selected modules passed the axiom audit.**
These counts include generated declarations and 12 private names, including
the three private Jordan--Wigner entry lemmas. The only observed axioms were
`propext`, `Classical.choice`, and `Quot.sound`; the maintained auditor rejects
other axioms and unsafe or partial declarations.

The [successful compiler and auditor job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423534561/job/131879141494)
used Lean `leanprover/lean4:v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The
[theorem contract](../../GRADED_CLIFFORD_STAR_RANK_CONTRACT.md) describes exact
hypotheses, carriers, conventions, and unproved extensions.

## What was checked

| Owner | Result | Audited declarations |
| --- | --- | ---: |
| [Cl11GradedAdjoint](../../../lean/InfoGeometry/Clifford/Cl11GradedAdjoint.lean) | Transpose-compatible Clifford and graded-tensor adjoints, including the homogeneous Koszul sign under star/parity compatibility | 27 |
| [GradedTensorCutRank](../../../lean/InfoGeometry/Clifford/GradedTensorCutRank.lean) | Native contraction-range rank, parity projections, and both factor-two bounds for an involutive controlled twist | 48 |
| [Cl11UntwistCutRank](../../../lean/InfoGeometry/Clifford/Cl11UntwistCutRank.lean) | Equality relating the actual native graded lift to independent ordinary tensor coordinates, and the resulting one-head rank bounds | 15 |
| [Cl11GradedProjectorDefects](../../../lean/InfoGeometry/Clifford/Cl11GradedProjectorDefects.lean) | Ordered-word identities and nonzero projector/scaling defects on the native weighted Clifford carrier | 67 |
| [FiniteRealAnticommutation](../../../lean/InfoGeometry/LinearAlgebra/FiniteRealAnticommutation.lean) | Even real dimension for invertible anticommuting operators and for real complex structures | 10 |
| [GradedUnrollingCounterexamples](../../../lean/InfoGeometry/Clifford/GradedUnrollingCounterexamples.lean) | Explicit failure of forced tripotence and of an obstruction based only on an odd outer matrix index | 30 |
| **Total** | **Six selected owners** | **197** |

The adjoint and untwist owners retain an arbitrary noncommutative real
coefficient algebra. The cut-rank construction assumes a finite-dimensional
left factor and allows an infinite-dimensional right factor. Finite right-tail
bounds state their additional finite-dimensionality hypotheses.

The three-generator example proves that the proposed normalized all-length
scaling already fails at three factors: the represented vacuum entry of
`p3^2 - p3/4` is `-1/32`. Each single-site factor is idempotent, and the first
two factors are proved not to commute. The matrix entry only detects a nonzero
element; its evaluation is not assumed multiplicative or faithful.

## Independent reconciliation and immutable evidence

- [Checker status](run-43423534561-status.json): exact revision, tree, pins,
  successful return codes for all 44 modules, all 44 source SHA-256 values,
  and the six audited owner counts.
- [Native audit markers](run-43423534561-audit.log): every native audit marker
  in its original order, with runner timestamp prefixes removed.
- [Independent QA report](final-qa-accepted-checkpoint.md) and
  [machine-readable reconciliation](final-qa-accepted-checkpoint.json): zero
  source-hash mismatches, zero duplicate declarations, count reconciliation,
  private-declaration coverage, and ten verification-control hashes.
- [Uploaded verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423534561/artifacts/14034992802):
  source closure, logs, and status. Uploaded ZIP SHA-256:
  `15a2535c8067b462b55c8119b5b56f47872c432b9d2bd5a9f9e635c2e5c587e2`.

The accepted local Git checkpoint is
`722881370030a13e61664d5d255899f566454c97`; its tree is identical to the
published checkpoint above. A documentation-only successor can use this
evidence after comparing all 44 source files and the recorded verification
controls byte for byte. Its own head and any further CI results are reported
separately in the PR; this record does not certify an unexamined successor.

The compiler was not run with warnings as errors. The successful run contains
20 warning headers: 5 from selected owners and 15 inherited. The independent
report lists the selected warnings. No warning-free claim is made.

## Exact validation commands

The scoped job used the checked-in workflow and harness:

```bash
python3 project/tools/quality/check_graded_clifford_star_rank.py \
  --mathlib-root pinned-mathlib --output verification
```

The harness checks the unchanged pins, copies the exact source closure to a
fresh directory, serializes compilation under the shared build lock, and then
runs the maintained native ownership/axiom auditor. It performs the audit only
after every closure module compiles. All imported repository modules are
compiled; the exhaustive declaration audit is specifically for the six new
owners.

The separately tracked staged proof and root gates are invoked by the workflow:

```bash
python3 tools/quality/proof_proxy_staged_gate.py
bash scripts/quality/post_build_gate.sh --incremental \
  --base="$TASK_BASE" --head="$TESTED_HEAD"
bash scripts/quality/post_build_gate.sh --full
```

The workflow constructs the actual task-base-to-head staged Lean range before
running the staged gate. `TASK_BASE` is
`ce34c806983f97e7ff3c95b5d06081bd93534c5b`; `TESTED_HEAD` is the fetched exact
revision for that job. The local tracked pre-commit gate also passed on the
final source checkpoint. The checkers, pins, and gates were not weakened to
obtain the focused result.

## Root-integration limitation

The [latest completed root-gate evidence retained here](run-43420674640-source-gates-summary.json)
is from revision `b910386b2fc215d154d50474783dd9212dfce8fc`:

| Check | Observed result |
| --- | --- |
| Staged proof gate on the actual task range | Passed |
| Incremental root quality gate | Failed before target compilation |
| Full root quality gate | Failed before root compilation |
| First blocking Lake error | Required package directory `external_refs/homotopy-hypothesis-lean4` is absent |

[Path inspection](root-path-prerequisites.json) confirms that this package and
the Atlas path have neither tracked contents nor submodule entries. The GIFT
dependency has a tracked gitlink. This task does not supply guessed external
revisions or modify root dependency configuration. Root diagnostics also
contain semantic-vacuity findings; a command returning zero is not interpreted
as a finding-free repository.

At the accepted kernel checkpoint, its separate source-gates job was queued.
The PR remains a draft with a scoped kernel result and an explicit integration
blocker. This is not a whole-repository acceptance certificate.

## Claim review and earlier failures

The [frozen source](../../intake/graded-clifford-star-rank/source.txt) and
[independent intake audit](../../intake/graded-clifford-star-rank/audit.md)
preserve the 24,406-byte attachment, its unfinished final sentence, and the
distinction between valid, conditional, false, and unproved claims.

The numbered semantic reviews are source-level reports. In particular,
[review 09](candidate-semantic-review-09.md) examines the final projector
source and its exact Jordan--Wigner entry lemmas. The checkpoint JSON files
whose names contain `failed` record prior compiler failures. Those runs did
not reach the native axiom audit and are not accepted proof evidence.

The result establishes the concrete one-head rank bridge and the six listed
owners. It does not claim arbitrary-length graded-terminal unrolling, all
tensor-train cuts, tensor-train minimality, homogeneous rank equality, sharpness
of the factor-two bound, an integral lattice-index theorem, categorical
bosonization, or analytic positivity. Recursive work with a purely even
terminal algebra remains in the separate PR #354.
