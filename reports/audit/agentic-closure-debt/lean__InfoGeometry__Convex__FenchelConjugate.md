# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.304982+00:00`
Root: `lean/InfoGeometry/Convex/FenchelConjugate.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/FenchelConjugate.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Convex/FenchelConjugate.lean`
- module: `InfoGeometry.Convex.FenchelConjugate`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `existential-packaging` in `lemma fenchelSet_nonempty` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L56 [advisory] `local-hypothesis-injection` in `theorem fenchelYoung` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [soft] `skeletal-proof` in `theorem fenchelYoung_eq_of_conj_eq` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem fenchelConj_eq_of_isGreatest` — proof appears to close via minimal tactic one-liner

