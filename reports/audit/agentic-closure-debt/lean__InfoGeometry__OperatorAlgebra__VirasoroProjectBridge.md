# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:26.361322+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/VirasoroProjectBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **0**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/VirasoroProjectBridge.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/VirasoroProjectBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.VirasoroProjectBridge`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [advisory] `existential-packaging` in `theorem virasoro_project_is_certified` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

