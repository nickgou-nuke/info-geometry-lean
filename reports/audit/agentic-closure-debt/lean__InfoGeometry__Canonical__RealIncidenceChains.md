# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:48.704662+00:00`
Root: `lean/InfoGeometry/Canonical/RealIncidenceChains.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RealIncidenceChains.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/RealIncidenceChains.lean`
- module: `InfoGeometry.Canonical.RealIncidenceChains`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L58 [soft] `skeletal-proof` in `theorem boundaryOne_apply` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `theorem boundaryOne_single` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `skeletal-proof` in `theorem boundaryOne_single_one` — proof appears to close via minimal tactic one-liner

