# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:25.385474+00:00`
Root: `lean/InfoGeometry/Core/SymmetricSpaces.lean`
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
| `lean/InfoGeometry/Core/SymmetricSpaces.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Core/SymmetricSpaces.lean`
- module: `InfoGeometry.Core.SymmetricSpaces`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L123 [soft] `simp-law-injection` in `simp-declaration CartanInvolution.toInvolutiveMulAut_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L128 [soft] `simp-law-injection` in `simp-declaration mem_fixedSubgroup_of_cartan_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `skeletal-proof` in `lemma symmetricPairOfCartan_K_eq_fixedSubgroup` — proof appears to close via minimal tactic one-liner
  - L155 [soft] `skeletal-proof` in `lemma symmetricPairOfInvolutiveMulAut_K_eq_fixed` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `skeletal-proof` in `lemma symmetricPairOfInvolutiveMulAut_K_eq_fixedSubgroup` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `simp-law-injection` in `simp-declaration symmetricSpaceOfCartan_symmetry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [soft] `simp-law-injection` in `simp-declaration symmetricSpaceOfInvolutiveMulAut_symmetry` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

