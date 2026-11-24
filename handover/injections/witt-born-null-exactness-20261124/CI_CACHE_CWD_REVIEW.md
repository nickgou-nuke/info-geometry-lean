# Independent review of the native-cache working-directory repair

Date: 2026-11-24. Reviewed candidate patch
`witt-born-candidates/ci-fix/native-cache-cwd.patch` and the integrated files
in `/tmp/info-geometry-zorn-primal-dual-20261124`.

| Integrated file | SHA-256 |
| --- | --- |
| `verification/zorn-primal-dual/check.py` | `26c187c9fe392a441a17f198b9dc9eb90034fa7bdbd4154f8ca6c23f7461bb2b` |
| `.github/workflows/zorn-witt-born.yml` | `98a55483d5bb3de8043dc3f815c8ead20c785b47907077cdaf01a99b06f10c8d` |

Both hashes match the candidate author report. This reviewer ran no syntax
test, compiler, build, cache retrieval, workflow mutation, or axiom audit.

## Observed failure and scope

The preserved receipt for GitHub run `45408330719` records merge-test revision
`43c90beb66cadff1f78f1ca9f19ed2ad967ec988`. The counterexample command returned
1 after 0.214 seconds, reporting a missing
`Batteries/Lean/Position.olean` at its first import. The receipt has
`audit_status: not-run`. This is a native dependency artifact failure before
theorem elaboration, not a failed mathematical proof and not a successful
native validation result.

## Independently inspected source cause

The old helper fixed every subprocess working directory to the root project.
Passing `lake -d <mathlib>` did not override that actual working directory:

- Pinned Lean `Lake/CLI/Main.lean` handles `--dir` by changing
  `LakeOptions.rootDir`.
- Its `exe` command delegates execution to `Lake.env`.
- `Lake/CLI/Actions.lean` implements `Lake.env` with `IO.Process.spawn`,
  passing the command, arguments, and augmented environment but no cwd.

Pinned Mathlib `Cache/IO.lean` determines whether it is at the Mathlib root by
checking the relative `Mathlib` path. Its `mkLeanTarConfig`, and the matching
`decompressBatch` in `Cache/Requests.lean`, add a base-directory override only
for Mathlib archives when running elsewhere. Non-Mathlib archives keep their
stored relative paths. The decompressor spawn also leaves cwd inherited.

These inspected definitions support the identified failure mechanism: cache
output for dependency modules can land relative to the wrong project root,
while the workflow later moves the separately nested dependency checkouts.
The uploaded receipt does not show the misplaced artifact itself, so its
precise former location remains a source-based inference.

## Repair review

The helper now accepts an optional keyword-only `cwd`, resolves it, uses it
for `Popen`, and records it in the command result. Omitting the argument
preserves the existing root-project directory for repository compilation and
audit callers. Child cleanup and inherited lock descriptors are unchanged.

The workflow runs both cache hydration and `lake build` for the same selected
native imports with actual `cwd=mathlib`, under the same maintained exclusive
lock, before moving the fresh dependency directories. This gives Lake the
correct ordinary workspace for any missing transitive build artifacts. Both
commands must succeed; both results are retained. Existing manifest hashes,
exact revisions, tracked cleanliness, checker identity, and layout checks
remain enforced after the build.

No dependency/toolchain pin, mathematical source, proof gate, axiom policy,
source target set, or cache-preservation rule is weakened by this patch.
There is no ad-hoc single-file artifact copy or build of the root's optional
dependency graph.

## Runtime thread setting

This reviewer independently fetched the official Lean v4.34.1 source:
https://github.com/leanprover/lean4/blob/v4.34.1/src/runtime/object.cpp

Its `get_lean_num_threads` reads `LEAN_NUM_THREADS`, and
`lean_init_task_manager` passes that result to task-manager initialization.
Thus setting this variable to `1` is a source-supported runtime setting for
the Lake/cache processes. It is not a proof that every subprocess or compiler
internal pool is single-threaded. Repository compilation retains explicit
`lean -j1`.

## Disposition

No blocking source-level defect was found in the minimal repair. The next
GitHub run must establish whether it fixes dependency hydration and reaches
native theorem elaboration. The locally blocked syntax recheck supplies no
passing test result; no other task's lock or process was altered.
