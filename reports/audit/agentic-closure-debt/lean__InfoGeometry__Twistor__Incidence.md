# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.858718+00:00`
Root: `lean/InfoGeometry/Twistor/Incidence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **1**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Twistor/Incidence.lean` | `advisory` | 12 | 0 | 1 | 10 | 11 |

## Findings by file

### `lean/InfoGeometry/Twistor/Incidence.lean`
- module: `InfoGeometry.Twistor.Incidence`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `skeletal-proof` in `lemma det_zero_of_annihilates_nonzero` — proof appears to close via minimal tactic one-liner
  - L71 [advisory] `local-hypothesis-injection` in `lemma det_zero_of_annihilates_nonzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L103 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L104 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L110 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L118 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [advisory] `local-hypothesis-injection` in `theorem incident_points_null_separated` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

