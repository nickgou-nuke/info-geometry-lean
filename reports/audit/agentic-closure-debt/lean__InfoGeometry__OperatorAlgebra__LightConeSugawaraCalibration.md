# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:17.793517+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/LightConeSugawaraCalibration.lean`
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
| `lean/InfoGeometry/OperatorAlgebra/LightConeSugawaraCalibration.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/LightConeSugawaraCalibration.lean`
- module: `InfoGeometry.OperatorAlgebra.LightConeSugawaraCalibration`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L152 [advisory] `local-hypothesis-injection` in `theorem virasoro_centralTerm_eq_zero_of_not_modeBalanced` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

