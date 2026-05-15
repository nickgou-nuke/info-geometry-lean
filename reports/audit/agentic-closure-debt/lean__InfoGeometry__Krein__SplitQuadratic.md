# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:54.525689+00:00`
Root: `lean/InfoGeometry/Krein/SplitQuadratic.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/SplitQuadratic.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/Krein/SplitQuadratic.lean`
- module: `InfoGeometry.Krein.SplitQuadratic`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L11 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [soft] `simp-law-injection` in `simp-declaration grad_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration metricOp_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `skeletal-proof` in `theorem metricOp_eq_cl11Rep_pseudoscalar` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `simp-law-injection` in `simp-declaration grad_eq_cl11Rep_pseudoscalar_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `skeletal-proof` in `lemma spectral_epsilon_selfAdj` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `skeletal-proof` in `lemma hasFDerivAt_grad` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `lemma hasFDerivAt_potential` — proof appears to close via minimal tactic one-liner
  - L69 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_potential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_potential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_potential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [soft] `simp-law-injection` in `simp-declaration inner_grad_eq_kreinInner` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

