# Two-boundary operator verification

This directory records the exact finite-matrix scope of the two-boundary
extension on base `cfbcbca21cf57a4614a9646768ba9356cf3cc6b0`.
The theorem contract is in `../../TWO_BOUNDARY_OPERATOR_CONTRACT.md`.

## Mathematical scope

The five new owners formalize instruments between positive boundaries,
complex-linear mixed readouts, semilinear reversal, matrix purification and
explicit noncommuting examples. Their carrier is the full complex matrix
algebra, with arbitrary dimension in the generic results. The sector carrier
retains all blocks. The tensor purification uses mathlib's native Kronecker product, column-first
`Matrix.vec` applied to the transpose and continuous functional calculus,
together with the repository's existing `Quantum.FinitePartialTrace` owner.

The concrete witnesses prove that the instrument normalizer is `7/18` while
the bare overlap is `4/9`; the weak readout is `(3 - I)/4`; reversing the
chronological operator order changes the weight from `5/72` to `1/8`.

## Verified result

Both independent fresh project-source runs passed: 31 modules per lane,
284 audited declarations including 230 theorem constants, 664 direct
proof-dependency edges, 359 Hasse edges and 10 layers. These counts include
existing owners and private/generated declarations. All 35 targeted tooling
regressions, strict refutation of the five new owners and the staged proof
gate passed. The nine owners and audit emitted no warnings; 95 warnings
per lane remain in unchanged dependencies, itemized in the QA receipt.

## Evidence

- `declaration-audit.jsonl` is the native audit of every declaration in the
  nine selected owners, including private and generated declarations.
- `dependency-order.json` is the unmodified output of
  `tools/quality/operator_geometry_dependency_order.py` for that audit. It
  contains the checked type/value dependency graph, topological layers and
  transitive reduction. Constructor/recursor metadata are outside this graph;
  their declarations remain in the safety and axiom audit.
- `lean-result.json` and `src-result.json` record the independently compiled
  project closures, source hashes, pinned dependencies and verification tools.
- `source-review.md` is the independent semantic/source review, bound to the
  source bytes. Its pending-native wording describes that earlier review
  stage; the separate QA receipt records the subsequent execution verdict.
- `qa-acceptance.json` records the independent QA commands, input identities,
  scoped checks and limitations.
- `frozen-inputs-before.json` and `frozen-inputs-after.json` preserve the
  84-file source/tool and runtime identity snapshots.
- `integrity-comparison.json` records the independent graph comparison.
- `qa-summary.md` provides the independent reviewer's readable verdict.
- `root-path-preflight.json` preserves the separate root integration blocker.
- `verification.json` indexes these receipts and their hashes.

The dependency relation is `a ≤ b` when `a = b` or the chosen checked type or
value of `b` transitively uses `a`. It describes these formal proofs, not a
physical causal order or a claim of unique mathematical necessity.

## Reproduction and scope boundary

Use `tools/quality/check_operator_geometry.py` with the recorded Lean and
mathlib pins, all nine recorded `--owner` values, the
`InfoGeometry.Quantum.KrausInvariantGeometry` consumer target,
`--audit --audit-source tools/quality/TwoBoundaryDeclarationAudit.lean`,
`--owner-warnings-as-errors`, and the recorded baseline reference. Repeat
with `--source-lane lean` and `--source-lane src` in separate fresh artifact
directories; do not reuse one lane's compiled project artifacts for the other.
The independent commands in the receipt do not use `--incremental`.

This checks freshly compiled project sources against pinned cached mathlib
artifacts. It is not a fresh build of mathlib itself. The host used a narrow
`readlink` compatibility helper solely to map the current process's
`/proc/<pid>/exe` lookup to `/proc/self/exe`; the receipt records both its
source and binary hashes. It does not replace Lean or supply proof results.

The managed root path preflight remains blocked: `HomotopyHypothesis` and
`Atlas` have missing untracked path configurations, and `GIFT` is an
uninitialized recorded gitlink. A scoped native acceptance does not certify
root Lake integration, the ordinary pre-push gate or a complete repository
build. This work is prepared for draft review; those gates remain required
before integration. No cosmological dynamics or physical predictions follow
from the finite operator theorems without additional mathematical hypotheses.
