# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:33.289554+00:00`
Root: `lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/PrimitivePrimeProjectiveTemperature.lean`
- module: `InfoGeometry.Arithmetic.PrimitivePrimeProjectiveTemperature`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `skeletal-proof` in `theorem arithmeticPrimeRestrictedPartition_eq` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `skeletal-proof` in `theorem arithmeticPrimeInvertedPartitionDensity_eq` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `theorem arithmeticPrimeRestrictedPartition_nonneg` — proof appears to close via minimal tactic one-liner
  - L90 [advisory] `local-hypothesis-injection` in `theorem arithmeticPrimeRestrictedPartition_eq_exp_sum_of_supportedAbove_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

