# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.326639+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKreinCompactOperator.lean`
- module: `InfoGeometry.KK.RealSplitKreinCompactOperator`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `skeletal-proof` in `lemma superComm_eps_isCompactOperator` — proof appears to close via minimal tactic one-liner
  - L28 [soft] `skeletal-proof` in `lemma superComm_J_isCompactOperator` — proof appears to close via minimal tactic one-liner
  - L34 [soft] `skeletal-proof` in `lemma superComm_pi_isCompactOperator` — proof appears to close via minimal tactic one-liner
  - L40 [soft] `skeletal-proof` in `lemma comm_isCompactOperator` — proof appears to close via minimal tactic one-liner

