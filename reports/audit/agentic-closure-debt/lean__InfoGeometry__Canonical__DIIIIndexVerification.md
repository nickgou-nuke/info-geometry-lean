# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:58.488826+00:00`
Root: `lean/InfoGeometry/Canonical/DIIIIndexVerification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DIIIIndexVerification.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/Canonical/DIIIIndexVerification.lean`
- module: `InfoGeometry.Canonical.DIIIIndexVerification`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `skeletal-proof` in `theorem z2IndexOfCount_val_eq_mod` — proof appears to close via minimal tactic one-liner

