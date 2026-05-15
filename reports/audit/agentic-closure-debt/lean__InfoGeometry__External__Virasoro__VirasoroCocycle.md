# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.489816+00:00`
Root: `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/VirasoroCocycle.lean`
- module: `InfoGeometry.External.Virasoro.VirasoroCocycle`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `skeletal-proof` in `lemma virasoroCocycleBilin_apply_lgen_lgen` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `lemma virasoroCocycleBilin_eq_neg_flip` — proof appears to close via minimal tactic one-liner
  - L69 [advisory] `local-hypothesis-injection` in `lemma virasoroCocycleBilin_eq_neg_flip` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L110 [advisory] `local-hypothesis-injection` in `def virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L123 [soft] `skeletal-proof` in `lemma bdry_lgen_lgen_neg_eq` — proof appears to close via minimal tactic one-liner

