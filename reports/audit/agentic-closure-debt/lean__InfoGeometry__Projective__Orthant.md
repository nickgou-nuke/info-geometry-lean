# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.364166+00:00`
Root: `lean/InfoGeometry/Projective/Orthant.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **1**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/Orthant.lean` | `advisory` | 5 | 0 | 1 | 3 | 4 |

## Findings by file

### `lean/InfoGeometry/Projective/Orthant.lean`
- module: `InfoGeometry.Projective.Orthant`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [soft] `skeletal-proof` in `lemma mem_positiveOrthantCone` — proof appears to close via minimal tactic one-liner
  - L50 [advisory] `local-hypothesis-injection` in `def positiveOrthant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `def positiveOrthant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

