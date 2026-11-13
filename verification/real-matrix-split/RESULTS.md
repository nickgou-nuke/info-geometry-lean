# Real matrix decomposition: verification results

## Scoped acceptance

The real-matrix source at published commit
`3ccf5664775950733e24b6113a022cbf63b82619`, tree
`700c4648345511e894b371c950b385ffceb254ac`, passed the focused Lake build,
a fresh transitive axiom audit, and strict source screening in GitHub Actions.
An independent non-authoring QA reviewer then initiated and inspected a second
execution against that same source tree.

This acceptance covers the seven mathematical owners listed in [README.md](README.md),
their aggregate import, and the explicit declaration audit. It does not certify
the root package, the mirrored `src/` lane, or all repository CI checks.

## Mathematical result

The implementation adds **53 theorem declarations and four concrete real matrix
definitions**, while retaining, recompiling, and auditing 24 existing public
declarations from two owners.
The audit covers all **81 explicitly named public declarations** across those
seven owners. The new results preserve the full ordered matrix products:

- Native real symmetric/skew half formulas, the square expansion, and
  `Mᵀ * M - M * Mᵀ = 2 • (G * Ω - Ω * G)`.
- Normality if and only if the two parts commute; congruence covariance.
- Native bilinear symmetry, alternation, and even dimension for a nondegenerate
  skew form.
- Raised-index skew-adjointness and bilinear evaluation under the stated
  determinant and symmetry hypotheses.
- The existing unit-weighted adjoint specialized to real matrices, with native
  adjoint-pair characterization, involution, reconstruction, and uniqueness.
- The supplied two-dimensional example, including positive definiteness,
  nondegeneracy, noncommutation, and `A² = -(1/4) • 1 ≠ -1`.

The complete hypotheses and reuse inventory are in
[REAL_MATRIX_SPLIT_CONTRACT.md](../../docs/REAL_MATRIX_SPLIT_CONTRACT.md).
No smooth manifold or closure statement `dω = 0` is claimed.

## Hosted build and axiom evidence

- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- [First successful focused execution](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981020/job/131793494358).
- [Independent rerun, attempt 2](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981020/job/131794588066).
- [Rerun artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981020/artifacts/14023388549).

The build uses pinned dependency/source artifacts and normal Lake tracking.
The separate `env lean` audit regenerates axiom output even when artifacts are
current. This is not described as a cache-free rebuild. All 81 public
declarations have exactly one axiom record, with dependencies confined to
`propext`, `Classical.choice`, and `Quot.sound`.

## Independent source checks

The independent source review and its preserved delta accepted the exact
hypotheses, carriers, product order, and finite scope. Their source-only status
is intentionally preserved; the later QA receipt supplies the build and
axiom evidence.

The distinct QA reviewer checked the 19-file source/configuration fingerprint,
strict source screening and refutation, the semantic-vacuity error gate,
regression for both existing owners, and all nine final indexed Lean blobs.
The post-commit staged CLI alone sees no staged change; it is not used as a
substitute for that explicit indexed-blob check.

Five heuristic warnings are ordinary weighted-adjoint map laws: the new
additivity, subtraction, and real scalar laws, and the two unchanged generic
multiplication laws. They were individually reviewed and retained. No
vacuous hypothesis, scalar surrogate, or proof placeholder was accepted.
The actual pre-commit staged proof hook also ran on the implementation commits.

## Repository integration boundary

The following failed jobs were inspected on the same published source
commit. Their offending files or configuration are unchanged from base
`a392af178af1fe2bcba2ba39eb405700c6ee103c`; none identifies a defect in the
17 task files. This is a bounded triage, not a claim that every baseline or
downstream target is correct.

| Workflow | Observed cause / boundary |
| --- | --- |
| [Lean style lint](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981145/job/131793494181) | Existing KRDualityCascade.lean/KrDualityCascade.lean filename collision; Lean lint never ran. |
| [Sorry Gate](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981036/job/131793493754) | 878 findings in 91 existing forensic/fixture files; none in the 17 task paths; Lake package findings: 0. |
| [CI / baseline](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981039/job/131793572733) | Missing HomotopyHypothesis and Atlas path packages, and uninitialized GIFT gitlink; baseline build blocked. |
| [Post-Build Quality Gate](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981142/job/131793494094) | Root Lake build stopped loading missing HomotopyHypothesis; actual quality-gate step skipped. |
| [Build thesis, blueprint, and docs](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981024/job/131793493978) | GitHub Pages configuration returned HTTP 404; later builds skipped. |
| [Reviewed PR Integration](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981166/job/131793494636) | Existing external_refs/auto-ontology gitlink lacks a .gitmodules URL; checkout failed. |
| [Closure Debt + Superorganism Smoke](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981048/job/131793493940) | Workflow Python lacks pytest; tests did not execute. |
| [Idempotent chart calculus (scoped)](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43397981265/job/131793494736) | Existing SyntaxError at tools/quality/check_operator_geometry.py:168; compilation did not start. |

The actual Post-Build Quality Gate did not run after its prerequisite root
build failed. No local pre-push or whole-repository success is claimed.
These integration blocks remain visible on the PR. Publishing for review
does not merge it.

## Reproduction and provenance

Use the exact commands in [README.md](README.md), through the shared-lock
wrapper. Root toolchain, dependency pins, gate scripts, and hook policy are
unchanged.

The records below are preserved byte-for-byte from their authors. Original
workspace paths inside them record provenance; the copies here provide the
publication archive.

| Record | Purpose |
| --- | --- |
| [qa.json](acceptance/qa.json) · [checksum](acceptance/qa.sha256) | Final independent focused acceptance |
| [static_results.json](acceptance/static_results.json) · [checksum](acceptance/static_results.sha256) | Exact static commands, results, file hashes, and warning classifications |
| [real_matrix_split_aa.json](acceptance/real_matrix_split_aa.json) · [checksum](acceptance/real_matrix_split_aa.sha256) | Preserved independent source review |
| [real_matrix_split_aa_delta2.json](acceptance/real_matrix_split_aa_delta2.json) · [checksum](acceptance/real_matrix_split_aa_delta2.sha256) | Final source-only proof/configuration delta review |
| [Build log](acceptance/real-matrix-split-build.log) | Raw build log from the independent rerun |
| [Fresh axiom log](acceptance/real-matrix-split-axioms.log) | Raw output of the separate audit invocation |
| [Checked revision log](acceptance/real-matrix-split-revision.log) | Actual CI checkout commit and tree |

The final QA record SHA-256 is
`c21e14432ab13379d734070deed19a1e2302aa9923e74d3b52911b2e7a66e0ab`.
The fresh axiom log SHA-256 is
`68ee2f8a2b715ec1c6d43bd025272e31da59d0487a124e717ed16a25fad28734`.
[SHA256SUMS](acceptance/SHA256SUMS) covers every archived evidence file.

The actual CI checkout commit was
`8cf45fe1ff995762eebb31141e9ff5a223b14209`. Its tree equals the checked source
tree above; the separate local and published commit IDs differ only in commit
metadata. QA also checked all eight declaration names containing apostrophes
and confirmed that missing, duplicate, unexpected, and unapproved-axiom
records are each rejected.

The source-only records and static-stage record retain their original
intermediate dispositions. The later acceptance receipt is the final scoped
QA observation. Record hashes establish byte integrity; they are not a
signature or an immutable-storage guarantee.

The follow-up that adds this report and the unchanged evidence records edits
no Lean proof, checked workflow, audit script, or build/dependency configuration.
