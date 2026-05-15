# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:08.648646+00:00`
Root: `lean/InfoGeometry/Canonical/Fock.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Fock.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/Fock.lean`
- module: `InfoGeometry.Canonical.Fock`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `skeletal-proof` in `theorem bayesianUpdate_eq_creationExcitation` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `theorem dataPart_eq_creation` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `theorem modelPart_eq_annihilation` — proof appears to close via minimal tactic one-liner

