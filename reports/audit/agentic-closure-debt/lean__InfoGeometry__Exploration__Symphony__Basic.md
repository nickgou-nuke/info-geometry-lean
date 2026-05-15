# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:28.551362+00:00`
Root: `lean/InfoGeometry/Exploration/Symphony/Basic.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Exploration/Symphony/Basic.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Exploration/Symphony/Basic.lean`
- module: `InfoGeometry.Exploration.Symphony.Basic`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `skeletal-proof` in `theorem symphony_cancellation` — proof appears to close via minimal tactic one-liner
  - L41 [advisory] `local-hypothesis-injection` in `theorem symphony_cancellation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L42 [advisory] `local-hypothesis-injection` in `theorem symphony_cancellation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L45 [advisory] `local-hypothesis-injection` in `theorem symphony_cancellation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L68 [advisory] `bridge-shaped-declaration` in `theorem active_projector_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

