# CI container and cache policy

- Main CI workflow: `.github/workflows/ci.yml`
- Container build/publish workflow: `.github/workflows/ci-container.yml`
- Container Dockerfile: `.github/ci/Dockerfile`

## Container publication

- The CI container image is `ghcr.io/nickgou-nuke/info-geometry-lean-ci`.
- Tags include:
  - `lean4-v4.28.1` (stable Lean toolchain tag used by CI probing)
  - `sha-<commit>` (immutable publish traceability)
  - `main` (trusted default branch publishes)
- Publishing is restricted to trusted events:
  - push to `main`
  - `workflow_dispatch`
- Pull requests can build the Dockerfile but do not publish.

## Main CI container consumption and fallback

- `ci.yml` probes `ghcr.io/nickgou-nuke/info-geometry-lean-ci:lean4-v4.28.1`.
- If available, CI validates `lean --version` from the container image.
- If unavailable (for example before first publication), CI emits a notice and continues on the host runner fallback path so PR validation remains usable.
- Digest/tag update path: after a successful trusted publish, update CI references intentionally (for example to a digest or updated maintained tag) in a normal reviewed PR.

## Lake cache policy

- Cached paths:
  - `~/.elan`
  - `.lake/packages`
  - `.lake/build`
- Cache key namespace:
  - `${runner.os}-lean4281-lake-${hashFiles(lean-toolchain,lakefile.lean,lake-manifest.json)}`
- Cache writes are restricted to trusted events only (push to `main` or manual dispatch), never arbitrary pull requests.

## Toolchain and manifest guardrails

- CI fails if required pinned files are missing.
- `lean-toolchain` must be exactly `leanprover/lean4:v4.28.1`.
- `lake-manifest.json` must parse as valid JSON.
- Installed Lean must report version `4.28.1`.
- Nested `.lake/packages` manifests are checked with `scripts/infra/enforce-v428-local-manifests.sh` when that directory exists.

## Prohibited cache-destructive commands

- Never run `lake clean`.
- Never delete `.lake`, `.lake/build`, or `.lake/packages` as part of CI.
- Keep build/test execution sequential in workflows and scripts.
