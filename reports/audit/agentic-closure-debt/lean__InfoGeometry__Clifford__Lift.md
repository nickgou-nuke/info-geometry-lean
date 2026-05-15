# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.135683+00:00`
Root: `lean/InfoGeometry/Clifford/Lift.lean`
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
| `lean/InfoGeometry/Clifford/Lift.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Clifford/Lift.lean`
- module: `InfoGeometry.Clifford.Lift`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L11 [soft] `simp-law-injection` in `simp-declaration Q11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L20 [soft] `skeletal-proof` in `lemma modular_j_complex_i_anticommute` — proof appears to close via minimal tactic one-liner
  - L32 [soft] `skeletal-proof` in `lemma cl11RepLin_apply_pair` — proof appears to close via minimal tactic one-liner
  - L39 [soft] `skeletal-proof` in `lemma cl11RepLin_sq` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `simp-law-injection` in `simp-declaration cl11Rep_` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `skeletal-proof` in `lemma cl11Rep_pseudoscalar` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `simp-law-injection` in `simp-declaration Q11_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `skeletal-proof` in `lemma cl11RepLin_apply_pair` — proof appears to close via minimal tactic one-liner

