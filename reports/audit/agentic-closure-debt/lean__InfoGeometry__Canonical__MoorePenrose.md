# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:32.339870+00:00`
Root: `lean/InfoGeometry/Canonical/MoorePenrose.lean`
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
| `lean/InfoGeometry/Canonical/MoorePenrose.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/MoorePenrose.lean`
- module: `InfoGeometry.Canonical.MoorePenrose`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L72 [soft] `skeletal-proof` in `theorem rightProjector_idempotent` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem leftProjector_idempotent` — proof appears to close via minimal tactic one-liner

