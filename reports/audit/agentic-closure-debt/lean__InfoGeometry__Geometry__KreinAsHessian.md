# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.988482+00:00`
Root: `lean/InfoGeometry/Geometry/KreinAsHessian.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **10**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/KreinAsHessian.lean` | `advisory` | 22 | 0 | 10 | 2 | 12 |

## Findings by file

### `lean/InfoGeometry/Geometry/KreinAsHessian.lean`
- module: `InfoGeometry.Geometry.KreinAsHessian`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [soft] `simp-law-injection` in `simp-declaration krein_hessian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `skeletal-proof` in `lemma krein_hessian_sq` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `simp-law-injection` in `simp-declaration krein_grad_eq_hessian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `skeletal-proof` in `lemma krein_hessian_eq_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `skeletal-proof` in `lemma hasFDerivAt_krein_grad` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `skeletal-proof` in `lemma hasFDerivAt_krein_potential` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `lemma krein_form_symm` — proof appears to close via minimal tactic one-liner
  - L94 [soft] `simp-law-injection` in `simp-declaration krein_form_to_doubled_real` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `simp-law-injection` in `simp-declaration krein_form_self_to_doubled_real` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration krein_potential_to_doubled_real` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

