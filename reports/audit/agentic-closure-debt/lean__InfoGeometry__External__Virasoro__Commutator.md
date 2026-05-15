# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:31.033163+00:00`
Root: `lean/InfoGeometry/External/Virasoro/Commutator.lean`
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
| `lean/InfoGeometry/External/Virasoro/Commutator.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/Commutator.lean`
- module: `InfoGeometry.External.Virasoro.Commutator`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `skeletal-proof` in `lemma commutator_comm` — proof appears to close via minimal tactic one-liner
  - L37 [soft] `skeletal-proof` in `lemma mul_eq_mul_add_commutator` — proof appears to close via minimal tactic one-liner
  - L41 [soft] `skeletal-proof` in `lemma commutator_pair` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `lemma commutator_pair'` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `simp-law-injection` in `simp-declaration commutator_smul_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L60 [soft] `simp-law-injection` in `simp-declaration smul_one_commutator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `simp-law-injection` in `simp-declaration commutatorBilin_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `skeletal-proof` in `lemma algebraCommutator'_apply` — proof appears to close via minimal tactic one-liner

