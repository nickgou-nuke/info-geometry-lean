# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:54.367084+00:00`
Root: `lean/InfoGeometry/Canonical/CliffordBridge.lean`
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
| `lean/InfoGeometry/Canonical/CliffordBridge.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/Canonical/CliffordBridge.lean`
- module: `InfoGeometry.Canonical.CliffordBridge`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L7 [soft] `skeletal-proof` in `theorem q_agrees_with_Gauge_quad` — proof appears to close via minimal tactic one-liner

