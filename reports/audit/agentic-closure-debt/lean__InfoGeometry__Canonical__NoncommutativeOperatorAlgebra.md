# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:33.656940+00:00`
Root: `lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **2**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/NoncommutativeOperatorAlgebra.lean`
- module: `InfoGeometry.Canonical.NoncommutativeOperatorAlgebra`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L101 [advisory] `existential-packaging` in `theorem exists_noncommuting_pair` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [soft] `skeletal-proof` in `theorem typeIII_baseIntegral_eq_modularWeight_integral` — proof appears to close via minimal tactic one-liner
  - L116 [soft] `skeletal-proof` in `theorem typeIII_coreTraceOfBase_eq_coreTrace_traceOfEmbedded` — proof appears to close via minimal tactic one-liner

