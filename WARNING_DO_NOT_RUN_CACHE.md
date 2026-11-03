# Lake cache preservation and recovery

Source reviewed on 2026-11-03 against
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. This page describes the current
wrapper behavior and cache-preservation policy. It does not assert that a
remote cache is available for the current machine or dependency revision.

## Preserve existing build artifacts

Never run `lake clean` or delete `.lake`, `.lake/build`, or `.lake/packages` as
a routine repair. Preserve [lean-toolchain](lean-toolchain),
[lakefile.lean](lakefile.lean), and [lake-manifest.json](lake-manifest.json)
unless the user explicitly authorizes a dependency/toolchain change. Normal
builds must remain able to write generated artifacts; do not make package
directories read-only.

Use the shared-lock wrappers from [RUNBOOK.md](RUNBOOK.md). They reject linked
Git worktrees and symlinked `.lake` or `.lake/packages` roots. Inspect active
compiler processes before validation and do not kill a running Lake process
without explicit user authorization.

## Existing automatic hydration

[tools/infra/build.py](tools/infra/build.py), in
`_ensure_mathlib_cache_hydrated`, checks whether
`.lake/packages/mathlib/.lake/build/lib/lean/Mathlib` contains any `.olean`
files. When the Mathlib directory exists but no such artifact is found, it
invokes `lake exe cache get` inside the locked build transaction before
launching the requested build. If any matching `.olean` exists, that helper
skips hydration; it is not a comprehensive cache-integrity check.

The helper uses `check=False` for that subprocess. Its invocation alone is
therefore not evidence of successful hydration. Inspect its output and the
subsequent build result. Cache retrieval and destructive cleaning are distinct
operations; the previous blanket assertion that the wrapper could never call
`cache get` contradicted this implementation.

Do not infer that upstream artifacts exist or are unavailable from a stale
warning. Diagnose the exact dependency, compiler error, and observed network
result. Preserve existing artifacts and use the smallest affected target for
recovery.

## Choose explicit validation coverage

For a known owner, use a targeted build, replacing the module name:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
```

When all registered default targets are the intended scope:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock --all-default-targets
```

The [wrapper](tools/infra/run_locked_lake_build.py) chooses changed-owner mode
when no target or `--all-default-targets` is supplied. That mode rejects extra
Lake arguments after `--`; in particular, the old no-target `-- -R` example
was not a valid recovery command. Additional Lake flags require an explicit
module/library target or `--all-default-targets`, and should be used only for
a diagnosed need. There is no universal forced-rebuild command that proves
all cache or source problems are repaired.

Record the exact command, selected scope, error/output, and exit result.
See [CI cache policy](docs/CI_CONTAINER_AND_CACHE_POLICY.md) for workflow-owned
cache handling and the [runbook](RUNBOOK.md) for proof acceptance.
