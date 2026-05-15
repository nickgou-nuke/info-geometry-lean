# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:47.960192+00:00`
Root: `lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Thermodynamics/ProjectiveTemperature.lean`
- module: `InfoGeometry.Thermodynamics.ProjectiveTemperature`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `skeletal-proof` in `theorem betaInvert_involutive` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem betaInvert_one` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem one_lt_betaInvert_of_mem_Ioo_zero_one` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `skeletal-proof` in `theorem one_isFixed_temperatureClosure` — proof appears to close via minimal tactic one-liner
  - L128 [advisory] `local-hypothesis-injection` in `theorem stereographicTemperature_on_unit_circle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

