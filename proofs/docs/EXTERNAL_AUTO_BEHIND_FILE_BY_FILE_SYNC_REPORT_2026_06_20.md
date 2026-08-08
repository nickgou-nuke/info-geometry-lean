# External `auto` behind file-by-file sync report — 2026-06-20

This records the actual behind-pass resolution after the ahead commits were audited. The goal was to compare the stale external worktree against current main file-by-file and only replace stale/weaker external content where current main was the repaired/better version.

## Actions

- Fetched `origin/main` in `/home/goutev/repos/info-geometry-lean/external_refs/auto`.
- Recomputed the behind-path inventory against current `/home/goutev/auto`.
- Copied current-main content into the external worktree only for paths that were missing or byte-different.
- Left the 679 already-identical paths untouched.
- Validated the external worktree with `cd proofs && lake build`.

## Resolution counts

- Behind paths compared: 720
- Already identical before copy: 679
- Missing in external and copied from current main: 8
- Different in external and replaced by current repaired/better version: 33
- Missing/different after copy: 0

## Why current main won for the 33 different paths

- 31 were the external-only Lean candidates already covered by `docs/EXTERNAL_CANDIDATE_NO_LOSS_AUDIT_2026_06_20.md`: current main contains repaired buildable theorem-honest modules; original external bytes remain recoverable from git history/backups.
- `proofs/lakefile.toml`: current main contains all external-ahead roots plus newer active roots; full build succeeds.
- `memory/2026-06-20.md`: current main contains the newer audit trail.

## Validation

- External worktree comparison after copy: all 720 behind paths match current main byte-for-byte.
- External `cd proofs && lake build`: succeeded.
- Pre-sync backup/status bundle: `/home/goutev/.trash-auto/external-auto-before-behind-sync-20260620-155834`.
