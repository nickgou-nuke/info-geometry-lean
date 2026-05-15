# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:46.428041+00:00`
Root: `lean/InfoGeometry/KK/KasparovCompactOperator.lean`
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
| `lean/InfoGeometry/KK/KasparovCompactOperator.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/KK/KasparovCompactOperator.lean`
- module: `InfoGeometry.KK.KasparovCompactOperator`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L23 [soft] `skeletal-proof` in `lemma superComm_isCompactOperator_of_even_rep` — proof appears to close via minimal tactic one-liner
  - L29 [soft] `skeletal-proof` in `lemma comm_isCompactOperator_of_mathlib_compact` — proof appears to close via minimal tactic one-liner

