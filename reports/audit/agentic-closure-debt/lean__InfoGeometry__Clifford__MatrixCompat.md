# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.269923+00:00`
Root: `lean/InfoGeometry/Clifford/MatrixCompat.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **2**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/MatrixCompat.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Clifford/MatrixCompat.lean`
- module: `InfoGeometry.Clifford.MatrixCompat`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [soft] `skeletal-proof` in `lemma baseJ1_sq` — proof appears to close via minimal tactic one-liner
  - L15 [soft] `skeletal-proof` in `lemma baseJ1_transpose` — proof appears to close via minimal tactic one-liner

