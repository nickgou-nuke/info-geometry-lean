# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:19.601453+00:00`
Root: `lean/InfoGeometry/Clifford/SplitQ11.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/SplitQ11.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Clifford/SplitQ11.lean`
- module: `InfoGeometry.Clifford.SplitQ11`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L10 [soft] `simp-law-injection` in `simp-declaration splitQ11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L21 [soft] `simp-law-injection` in `simp-declaration splitB11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L23 [soft] `skeletal-proof` in `lemma splitB11_expand` — proof appears to close via minimal tactic one-liner
  - L24 [soft] `simp-law-injection` in `simp-declaration splitB11_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L27 [soft] `skeletal-proof` in `lemma splitQ11_eq_splitB11_diag` — proof appears to close via minimal tactic one-liner
  - L29 [soft] `simp-law-injection` in `simp-declaration splitQ11_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `theorem splitQ11_sub` — proof appears to close via minimal tactic one-liner

