# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.351876+00:00`
Root: `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **21**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean` | `advisory` | 43 | 0 | 21 | 1 | 22 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- module: `InfoGeometry.External.Virasoro.VirasoroAlgebra`
- status: `advisory`
- debt_score: `43`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L84 [soft] `skeletal-proof` in `lemma bracket_def'` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `simp-law-injection` in `simp-declaration bracket_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `simp-law-injection` in `simp-declaration bracket_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `skeletal-proof` in `lemma add_def'` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `skeletal-proof` in `lemma smul_def'` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `simp-law-injection` in `simp-declaration add_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `simp-law-injection` in `simp-declaration add_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration smul_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `simp-law-injection` in `simp-declaration smul_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `skeletal-proof` in `lemma cgen_eq_ofCentral_one` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `lemma cgen_eq'` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `lemma lgen_eq'` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `simp-law-injection` in `simp-declaration ofCentral_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `simp-law-injection` in `simp-declaration toWittAlgebra_cgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration toWittAlgebra_lgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `simp-law-injection` in `simp-declaration cgen_bracket` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L144 [soft] `simp-law-injection` in `simp-declaration bracket_cgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `simp-law-injection` in `simp-declaration lgen_bracket` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L172 [soft] `simp-law-injection` in `simp-declaration lsection_lgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L195 [soft] `simp-law-injection` in `simp-declaration basisLC_some` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L199 [soft] `simp-law-injection` in `simp-declaration basisLC_none` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

