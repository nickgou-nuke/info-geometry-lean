# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:31.744856+00:00`
Root: `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **24**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean` | `advisory` | 50 | 0 | 24 | 2 | 26 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/HeisenbergAlgebra.lean`
- module: `InfoGeometry.External.Virasoro.HeisenbergAlgebra`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L70 [soft] `skeletal-proof` in `lemma jgen_eq_single` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration lie_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `skeletal-proof` in `lemma heisenbergCocycleBilin_apply_jgen_jgen` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `lemma bracket_def'` — proof appears to close via minimal tactic one-liner
  - L205 [soft] `simp-law-injection` in `simp-declaration bracket_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L208 [soft] `simp-law-injection` in `simp-declaration bracket_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L214 [soft] `skeletal-proof` in `lemma add_def'` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `lemma smul_def'` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `simp-law-injection` in `simp-declaration add_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L223 [soft] `simp-law-injection` in `simp-declaration add_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L226 [soft] `simp-law-injection` in `simp-declaration smul_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L229 [soft] `simp-law-injection` in `simp-declaration smul_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `skeletal-proof` in `lemma kgen_eq_ofCentral_one` — proof appears to close via minimal tactic one-liner
  - L245 [soft] `skeletal-proof` in `lemma kgen_eq'` — proof appears to close via minimal tactic one-liner
  - L247 [soft] `skeletal-proof` in `lemma jgen_eq'` — proof appears to close via minimal tactic one-liner
  - L249 [soft] `simp-law-injection` in `simp-declaration ofCentral_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L253 [soft] `skeletal-proof` in `lemma toAbelianLieAlgebraOn_kgen` — proof appears to close via minimal tactic one-liner
  - L256 [soft] `simp-law-injection` in `simp-declaration toAbelianLieAlgebraOn_jgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L259 [soft] `simp-law-injection` in `simp-declaration lie_kgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L263 [soft] `simp-law-injection` in `simp-declaration lie_jgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L279 [soft] `simp-law-injection` in `simp-declaration jsection_jgen` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L301 [soft] `simp-law-injection` in `simp-declaration basisJK_some` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L305 [soft] `simp-law-injection` in `simp-declaration basisJK_none` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L309 [soft] `simp-law-injection` in `simp-declaration lie_jgen_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

