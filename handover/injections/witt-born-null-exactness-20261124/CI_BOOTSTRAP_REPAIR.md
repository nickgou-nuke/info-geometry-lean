# CI failure and minimal native-cache correction

## Observed CI result

- PR head: `603faa37744b57392655dbd04f3aae58f027f74b`.
- Workflow run: `45408330719`; job: `138494989275`.
- Checked GitHub pull-request merge revision: `43c90beb66cadff1f78f1ca9f19ed2ad967ec988`.
- Source checkout, pinned Lean installation, native cache preparation, evidence collection, and evidence upload succeeded.
- Counterexample compilation failed at its first import; no repository module completed and no axiom audit ran. Full PR compilation was skipped.
- Exact diagnostic at 2026-11-24 13:56:08 UTC:

```text
SuppliedTableCounterexample.lean:6:0: error: object file
'/home/runner/work/_temp/zorn-witt-native-packages/batteries/.lake/build/lib/lean/Batteries/Lean/Position.olean'
of module Batteries.Lean.Position does not exist
```

The cache command had reported 3176 files downloaded and decompressed successfully. This is a missing native artifact, not a mathematical theorem diagnostic.

Evidence artifact:
https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45408330719/artifacts/14927341641

## Source-backed cause

`checker.execute` currently runs every child with `cwd=ROOT`. The workflow passed `lake -d <mathlib> exe cache get ...`, which selects Mathlib's package configuration but does not change the cache executable's actual working directory.

Pinned Lean source makes this distinction explicit:

- `Lake/CLI/Main.lean:339`: `--dir` updates `LakeOptions.rootDir`.
- `Lake/CLI/Main.lean:1173`: `lake exe` builds the executable, then delegates to `Lake.env`.
- `Lake/CLI/Actions.lean:20`: `Lake.env` spawns the executable with its augmented environment and no working-directory override.

Pinned Mathlib `Cache/IO.lean:469` (`mkLeanTarConfig`) redirects unpacked Mathlib artifacts when executing outside Mathlib, but leaves non-Mathlib archives with their stored relative paths. Its `spawnLeanTarDecompress` also does not override cwd.

Therefore third-party dependency archives can unpack beneath the project cwd while their source checkouts remain nested under the separate Mathlib checkout. Moving those nested source checkouts then leaves the desired flat package path without the downloaded artifacts. This explains the observed missing Batteries file. The actual misplaced file path was not included in the uploaded evidence, so its location remains a source-based inference rather than a directly inspected runner filesystem fact.

## Candidate changes

`native-cache-cwd.patch` changes only:

1. `verification/zorn-primal-dual/check.py`: add optional keyword-only `cwd`, defaulting to the existing ROOT; use it for the child and record it in the result. Existing compiler/audit callers keep their behavior. Lock inheritance and child cleanup are unchanged.
2. `.github/workflows/zorn-witt-born.yml`: run native cache hydration with actual `cwd=mathlib`; then run the parent's requested `lake build` for the same direct native imports under the same exclusive lock, before relocation. Preserve all existing post-build source/pin/manifest checks and record both commands.

No ad-hoc missing-module build list, modified dependency source, gate weakening, pin change, or root Lake build is introduced.

## Resource control

Pinned Lake's CLI help/parser does not expose `--jobs` or `-j`. Do not add an unsupported flag. The official Lean v4.34.1 `src/runtime/object.cpp` implementation of `get_lean_num_threads` reads `LEAN_NUM_THREADS`; the candidate sets it to `1` for the Lake/cache processes. This limits that runtime's worker pool; it is not a claim that every child compiler uses a one-thread internal pool. Repository owner compilation retains the checker's explicit `lean -j1`.

Primary source fetched through the GitHub connector:
https://github.com/leanprover/lean4/blob/v4.34.1/src/runtime/object.cpp
Blob SHA: `9a8b4c56809b160055d83f5c7e7b64e6191aa86c`.

## Candidate hashes and validation

- `check.py`: `26c187c9fe392a441a17f198b9dc9eb90034fa7bdbd4154f8ca6c23f7461bb2b`.
- `zorn-witt-born.yml`: `98a55483d5bb3de8043dc3f815c8ead20c785b47907077cdaf01a99b06f10c8d`.

Source review only. No local compiler, build, test, cache fetch, YAML parser, GitHub rerun/cancel, or repository mutation was performed by this worker. Parent review and the next actual workflow run must validate this correction.
