# Independent QA-A: accepted scoped kernel checkpoint

**Accepted:** all 44 repository-local closure modules compiled, and the maintained
native ownership audit passed for all 197 declarations owned by the six selected
modules. This is a scoped Lean kernel and declaration-audit result; repository-wide
integration is reported separately below.

## Exact identity

- Published commit: `ec36632a52860b8e710cd6b1c258a5c6f649d06e`.
- Published tree: `21b365c94f4e44fb853d342c7f7ecc04f07be35b`.
- Identical local tree at commit: `722881370030a13e61664d5d255899f566454c97`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- [Compiler/auditor job](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423534561/job/131879141494)
  in run `43423534561` completed successfully.

QA compared every compiler-recorded source SHA-256 with the accepted local Git
snapshot: **44 of 44 match, zero mismatches**. The local and remote tree IDs also
match. The companion JSON records every source hash, the six owner hashes, and ten
checker/workflow/auditor/gate/toolchain/manifest hashes.

## Native declaration reconciliation

| Selected owner | Audited declarations |
| --- | ---: |
| `Clifford.Cl11GradedAdjoint` | 27 |
| `Clifford.GradedTensorCutRank` | 48 |
| `Clifford.Cl11UntwistCutRank` | 15 |
| `Clifford.Cl11GradedProjectorDefects` | 67 |
| `LinearAlgebra.FiniteRealAnticommutation` | 10 |
| `Clifford.GradedUnrollingCounterexamples` | 30 |
| **Total** | **197** |

QA independently counted 197 distinct `AUDIT_DECL` markers and reconciled them
against every per-owner marker, the single total marker, and the checker status.
There were no duplicate declaration markers. The audited list contains **12 private
names**, including all three new Jordan--Wigner entry lemmas; generated proof and
pattern-matching declarations are included by native module ownership.

The only observed axioms were exactly `propext`, `Classical.choice`, and
`Quot.sound`. The maintained auditor rejects every other axiom and every unsafe or
partial declaration; successful completion covers every selected owned declaration.
No private-declaration exemption or public-name-only filter was introduced.

## Warnings and separate gates

This was **not** a warnings-as-errors run. The compiler emitted 20 warning headers:
5 from the selected owners and 15 inherited. Selected warnings concern two unused
section hypotheses, one proof-local `letI` style suggestion, one unused simp
argument, and one deprecated real-number import. The immutable job log retains
the complete warnings.

At this review checkpoint, the source-gates job for the accepted commit remained
queued. The previous published revision `21211692cf87418572b56aee50c5bf3337e48782`
had passed the unchanged staged proof gate and was running the root checks. The
latest completed root-gate evidence, run `43420674640` at revision
`b910386b2fc215d154d50474783dd9212dfce8fc`, records:

- Staged proof gate: **passed** on the actual base/head Lean range.
- Incremental root gate: **failed** before target compilation.
- Full root gate: **failed** before root compilation.
- Both failures: missing `external_refs/homotopy-hypothesis-lean4` required by the
  unchanged root Lake configuration.

Read-only Git inspection confirms that this missing path and the Atlas path have
no tracked gitlink or submodule entry; GIFT does. No dependency pin was inferred or
changed. Other completed root commands returned success, but the repository-wide
semantic-vacuity report remains diagnostic and contains findings. There is no
finding-free or full-repository acceptance claim.

## Evidence and publication boundary

The [verification artifact](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43423534561/artifacts/14034992802)
contains the copied closure source, compiler logs, status, and native audit.
Its uploaded ZIP SHA-256 is
`15a2535c8067b462b55c8119b5b56f47872c432b9d2bd5a9f9e635c2e5c587e2`.

Companion evidence:

- `run-43423534561-status.json`: exact checker status extracted from the job log.
- `run-43423534561-audit.log`: all native audit markers in their original order,
  after removing runner timestamp prefixes.
- `final-qa-accepted-checkpoint.json`: independently reconciled counts and hashes.
- `run-43420674640-source-gates-summary.json`: completed root-gate evidence.

A documentation-only successor may refer to this focused result only after an
independent comparison confirms unchanged bytes for all 44 closure sources and
all recorded verification controls. Its final Git head/tree and any new CI outcomes
must be reported explicitly. This review does not pre-certify an unexamined successor.

QA-A authored no mathematical source or repairs, ran no local Lean/Lake compiler,
and made no GitHub writes. Earlier failed runs remain separately identified and
were never promoted to accepted evidence.
