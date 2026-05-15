# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:56.623999+00:00`
Root: `lean/InfoGeometry/Canonical/CoordinateFree.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **2**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CoordinateFree.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/CoordinateFree.lean`
- module: `InfoGeometry.Canonical.CoordinateFree`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L20 [soft] `skeletal-proof` in `theorem coordinateFreeContract` — proof appears to close via minimal tactic one-liner

