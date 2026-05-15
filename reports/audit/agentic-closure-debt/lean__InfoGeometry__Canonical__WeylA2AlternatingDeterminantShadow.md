# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:10.312613+00:00`
Root: `lean/InfoGeometry/Canonical/WeylA2AlternatingDeterminantShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **0**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylA2AlternatingDeterminantShadow.lean` | `advisory` | 3 | 0 | 0 | 3 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylA2AlternatingDeterminantShadow.lean`
- module: `InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L78 [advisory] `bridge-shaped-declaration` in `theorem alternating_determinant_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

