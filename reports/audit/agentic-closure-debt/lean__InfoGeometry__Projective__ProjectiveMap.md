# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.720216+00:00`
Root: `lean/InfoGeometry/Projective/ProjectiveMap.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/ProjectiveMap.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Projective/ProjectiveMap.lean`
- module: `InfoGeometry.Projective.ProjectiveMap`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `skeletal-proof` in `lemma map_smul_gauge` — proof appears to close via minimal tactic one-liner
  - L47 [soft] `skeletal-proof` in `lemma projectiveMap_mk` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `lemma projectiveMap_vacuum` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `skeletal-proof` in `lemma projectiveMap_mk_gauge` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `lemma projectiveMapEven_mk` — proof appears to close via minimal tactic one-liner
  - L107 [soft] `skeletal-proof` in `lemma modular_j_gauge_equivariant` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `lemma spectral_epsilon_gauge_equivariant` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `lemma complex_i_gauge_equivariant` — proof appears to close via minimal tactic one-liner

