# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.096376+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **18**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularOperator.lean` | `advisory` | 37 | 0 | 18 | 1 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularOperator.lean`
- module: `InfoGeometry.Canonical.RelativeModularOperator`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularOperator_eq_diagMatrix_density` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularOperator_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularOperator_diag_eq_exp_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.log_modularOperator_diag_eq_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration RelativeStatePair.modularPotential_eq_neg_log_modularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L103 [soft] `simp-law-injection` in `simp-declaration relativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `simp-law-injection` in `simp-declaration relativeModularOperator_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration relativeModularOperator_diag_eq_exp_relativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_eq_log_relativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_eq_neg_log_relativeModularOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration relativeModularOperator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L191 [soft] `simp-law-injection` in `simp-declaration relativeModularVolumeShadow_eq_prod_relativeDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [soft] `simp-law-injection` in `simp-declaration relativeModularVolumeShadow_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L209 [soft] `simp-law-injection` in `simp-declaration relativeModularVolumeShadow_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L290 [soft] `simp-law-injection` in `simp-declaration relativeModularVolumePotential_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L314 [soft] `simp-law-injection` in `simp-declaration relativeModularBerezinianShadow_pos` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L448 [soft] `simp-law-injection` in `simp-declaration relativeModularHamiltonianReadout_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

