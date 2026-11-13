# Independent focused-checker source review

Status: source review only; no Lean/Lake compilation, tests, or GitHub writes.

The candidate checkout is based on `ce34c806983f97e7ff3c95b5d06081bd93534c5b`.
Exact reviewed file hashes are in `checker-source-review.json`. Candidate mathematical
owners are independently source-audited by the intake auditor; this review concerns
acceptance plumbing and evidence scope.

## Reviewed properties

- The workflow selects the pull request head SHA, rather than implicitly certifying a
  potentially different merge revision. Its source checkout is fresh and independent.
- The checker reads the root dependency manifest, verifies the exact Mathlib Git
  revision and toolchain match, and does not change those pins.
- The maintained closure resolver traverses repository imports, rejects unresolved
  repository imports and cycles, and records source bytes for every selected closure
  module. It copies these bytes into a fresh source tree and places a fresh output
  library first in LEAN_PATH.
- Compilation is serialized under the shared lock; another active Lean/Lake compiler
  is rejected. Each module is compiled directly, in dependency order. Failed imports
  block dependents and prevent the axiom audit from running.
- The maintained native auditor selects declarations by imported module ownership.
  It includes private and generated declarations, rejects unsafe/partial declarations,
  rejects axioms beyond propext/Classical.choice/Quot.sound, requires each mathematical
  owner to contribute declarations, and reconciles per-owner and total counts.
- Commit, tree, toolchain, Mathlib revision, source hashes, module outcomes, and audit
  counts are recorded. Artifacts retain the copied source and compiler/audit logs.
- The actual staged range is reconstructed in a separate job; its tree is checked
  against the tested tree and its Lean path list against the base/head diff.
- Incremental and full root quality gates are distinct attempted steps. Focused
  kernel success does not imply either root gate succeeded.

## Boundaries and follow-up

- No compiler result has yet been observed for this candidate snapshot.
- The current checker does not treat compiler warnings as errors. Preserve warnings
  in the final acceptance record; do not report a warnings-as-errors result.
- The planned projector owner must be added to the selected targets and workflow
  paths before claiming its acceptance.
- Before final acceptance, compare the remote workflow's recorded head/tree and
  owner/closure hashes with the published PR snapshot, reconcile every audit marker,
  and retain source-gate/root-gate results separately.
- For documentation-only final commits, verify mathematical and checker/workflow
  sources are byte-identical to the accepted code checkpoint before transferring
  focused acceptance. Never transfer evidence across a changed proof or checker.

No source-review acceptance blocker was identified in the inspected checker/workflow.
