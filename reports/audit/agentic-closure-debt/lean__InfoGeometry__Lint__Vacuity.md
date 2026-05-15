# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.173874+00:00`
Root: `lean/InfoGeometry/Lint/Vacuity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **1**
- Soft: **0**
- Advisory: **2**
- File status counts: clean=0, advisory=0, open_gap=1

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Lint/Vacuity.lean` | `open_gap` | 7 | 1 | 0 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Lint/Vacuity.lean`
- module: `InfoGeometry.Lint.Vacuity`
- status: `open_gap`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L142 [advisory] `existential-packaging` in `def classifyStatementShape` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L195 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

