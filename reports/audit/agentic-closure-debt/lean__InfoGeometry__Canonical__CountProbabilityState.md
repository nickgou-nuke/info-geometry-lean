# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:57.676673+00:00`
Root: `lean/InfoGeometry/Canonical/CountProbabilityState.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **0**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CountProbabilityState.lean` | `advisory` | 4 | 0 | 0 | 4 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/CountProbabilityState.lean`
- module: `InfoGeometry.Canonical.CountProbabilityState`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `local-hypothesis-injection` in `theorem empiricalProbabilityState_spec` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L28 [advisory] `local-hypothesis-injection` in `theorem empiricalProbabilityState_spec` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L32 [advisory] `existential-packaging` in `theorem exists_empiricalProbabilityState` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

