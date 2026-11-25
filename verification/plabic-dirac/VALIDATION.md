# Verification record

## Current status

**Compiler acceptance is pending.** The mathematical source review is complete,
but the repaired owner modules have not yet completed Lean elaboration and the
final native axiom audit has not run. Absence of placeholder tokens is not a
substitute for those checks.

The initial exact-pin pass compiled these retained repository dependencies:

- `InfoGeometry.Algebra.FiniteSpinAlgebra`
- `InfoGeometry.Meta.Architecture`
- `InfoGeometry.Clifford.NeutralPhaseSpaceCore`

It then reported errors in the predecessor `SkewGraphNeutralPairing` source:
two linear-map simplification failures and parser-invalid local identifiers.
The repairs distribute linear maps over addition/negation and rename the local
variables. No statement or hypothesis changed. The independent source review
records the repaired source hashes in `REVIEW.md`.

The resumed check was queued on the existing `/tmp/info-geometry-build.lock`.
Initially the holder was the earlier interactive
`courant-dirac-development` verifier. It subsequently released the lock and the
queued `dirac-plabic-coarse:5` check acquired it. Lock ownership alone does not
distinguish active Lean elaboration from a controller waiting for its next input.
No lock bypass or termination of another task was performed.

The queue subsequently advanced to `wilson-observable-focused-build`. The root
file wrapper then ran and stopped during package resolution because
`external_refs/homotopy-hypothesis-lean4` is absent.

The isolated retry reached its environment checks, but a toolchain relocation
changed Lake's resolved compiler path while preserving the executable hash and
version. The original lexical toolchain path now points to that relocated
runtime. The verifier now preserves the sibling Lean path of an explicit Lake
executable only after checking that its bytes match the compiler resolved by
Lake, and records both paths. The failed preflight and its logs were archived;
the original failed source-run report and six logs were restored bit-for-bit,
including modification times, with a separate recovery receipt. The next
isolated retry was queued. Its process handle is no longer available and no
completed result has been observed. No new mathematical source was compiled by
that failed preflight. The repaired-owner check therefore remains pending.

The publication pre-push gate initially rejected
`verification/plabic-dirac/PlabicDeclarationAudit.lean` because the root gate
does not route Lean sources at that path. The audit source has been moved
unchanged to `lean/InfoGeometry/Geometry/PlabicDeclarationAudit.lean`, which is
within the normal module tree. The isolated verifier now reads that path and
still runs the audit afresh. No gate or dependency pin was changed.

## Pinned environment

- Repository base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`
- Lean toolchain: `leanprover/lean4:v4.34.1`
- Lean executable version: 4.34.1, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Mathlib's eight dependency revisions were checked against both manifests.

No toolchain or dependency pin was changed. The task checkout has an independent
Git directory and does not use symlinked Lake package or build roots.

## Check scopes

| Check | Observed result |
| --- | --- |
| Mathematical source review | Accepted for the exact contract in `THEOREM_CONTRACT.md` |
| Exact compiler and Mathlib environment probe | Passed |
| Three retained foundational modules | Compiled successfully |
| Initial graph owner elaboration | Failed; source repaired afterward |
| Repaired graph, mirror, matrix and network owners | Pending; no completed retry result observed |
| Native all-owned-declaration axiom audit | Pending compilation |
| Independent native audit reconciliation | Pending native audit |
| Maintained root file wrapper | Failed during package resolution: missing `external_refs/homotopy-hypothesis-lean4` |
| Maintained root Lake owner build | Attempt exited 2 before compilation: shared lock held by `dirac-plabic-coarse:5` |
| Staged proof/source gate | Passed on the final Lean source snapshot during the commit hook (`proof_proxy_staged_gate: ok`) |
| Staged whitespace check | Passed after source repairs |

## Reproduction

From this checkout, with the exact Mathlib cache and compiler available:

```sh
python3 verification/plabic-dirac/verify.py \
  --mathlib /workspace/scratch/3288f93e1961/validation \
  --work /tmp/plabic-dirac-verification \
  --lake /workspace/scratch/3288f93e1961/runtime/lean-4.34.1-linux/bin/lake \
  --wait --adopt-completed
```

The one-time `--adopt-completed` option is restricted to the three successful
prerequisites from the inspected failed run. It archives that report and its
logs, checks source/compiler/configuration identities and artifact timestamps,
and labels its artifact hashes as sampled after the failure. It does not claim
that those hashes had previously been persisted. Subsequent retries use
`--resume`, which requires successful per-module source/import/artifact hash
receipts. A fresh output directory uses neither option and compiles the entire
reachable repository source closure.

The verifier checks added owners with `-DwarningAsError=true`. Its final native
audit enumerates declarations by actual module ownership, including generated
and private declarations, rejects unsafe/partial/local-axiom declarations, and
allows only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.
The independent Python reconciliation checks the complete audit output and
counts; it cannot replace a successful Lean invocation.

The maintained repository commands are separate checks:

```sh
python3 tools/infra/run_locked_lean.py \
  --wait-for-build-lock \
  lean/InfoGeometry/Geometry/PlabicDiracCourantUnification.lean
python3 tools/infra/run_locked_lake_build.py \
  --wait-for-build-lock --wfail \
  InfoGeometry.Geometry.PlabicDiracCourantUnification
```

The observed nonwaiting root-build attempt used the same target and `--wfail`
without `--wait-for-build-lock`. The maintained wrapper reported the occupied
lock and refused a concurrent build; that result is not a Lean compilation.

This record does not claim a successful root-package build, a repository-wide
build, a completed native axiom audit, or formalization of the physical and
differential-geometric interpretations excluded by the theorem contract.
