# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:17.281810+00:00`
Root: `lean/InfoGeometry/Clifford/Decomposition.lean`
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
| `lean/InfoGeometry/Clifford/Decomposition.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/Clifford/Decomposition.lean`
- module: `InfoGeometry.Clifford.Decomposition`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `skeletal-proof` in `lemma mem_k_iff` — proof appears to close via minimal tactic one-liner
  - L46 [soft] `skeletal-proof` in `lemma mem_p_iff` — proof appears to close via minimal tactic one-liner
  - L80 [advisory] `local-hypothesis-injection` in `lemma mem_p_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

