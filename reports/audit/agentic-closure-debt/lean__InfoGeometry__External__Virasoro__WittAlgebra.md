# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.759352+00:00`
Root: `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/WittAlgebra.lean`
- module: `InfoGeometry.External.Virasoro.WittAlgebra`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L65 [soft] `skeletal-proof` in `lemma lgen_eq_single` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration bracket_lgen_lgen'` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `lemma bracket_lgen_lgen'` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `lemma bracket_antisymm` — proof appears to close via minimal tactic one-liner
  - L95 [advisory] `local-hypothesis-injection` in `lemma bracket_self` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L120 [soft] `skeletal-proof` in `lemma bracket_leibniz` — proof appears to close via minimal tactic one-liner
  - L148 [soft] `simp-law-injection` in `simp-declaration bracket_lgen_lgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

