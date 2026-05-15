# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:27.478012+00:00`
Root: `lean/InfoGeometry/Canonical/ManifoldDegreeCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **1**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ManifoldDegreeCore.lean` | `advisory` | 4 | 0 | 1 | 2 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/ManifoldDegreeCore.lean`
- module: `InfoGeometry.Canonical.ManifoldDegreeCore`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [advisory] `existential-packaging` in `theorem exists_isolating_nhds_of_discrete` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L21 [soft] `skeletal-proof` in `theorem exists_isolating_nhds_of_discrete` — proof appears to close via minimal tactic one-liner

