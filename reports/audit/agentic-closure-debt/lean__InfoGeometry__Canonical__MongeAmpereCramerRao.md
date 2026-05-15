# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:32.079523+00:00`
Root: `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **7**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean` | `advisory` | 19 | 0 | 7 | 5 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/MongeAmpereCramerRao.lean`
- module: `InfoGeometry.Canonical.MongeAmpereCramerRao`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [soft] `simp-law-injection` in `simp-declaration cramerRaoMetricVolumePotential_eq_neg_logAbsDet` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `skeletal-proof` in `theorem absDet_cramerRaoMetric_eq_one_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem cramerRaoMetricVolumePotential_eq_zero_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L78 [advisory] `local-hypothesis-injection` in `theorem cramerRaoMetricVolumePotential_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [soft] `skeletal-proof` in `theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L102 [advisory] `local-hypothesis-injection` in `theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L104 [advisory] `local-hypothesis-injection` in `theorem logAbsDet_cramerRaoMetric_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L122 [soft] `simp-law-injection` in `simp-declaration squeezingEigen_product_eq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `simp-law-injection` in `simp-declaration squeezingLogShear_eq_four_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `simp-law-injection` in `simp-declaration abs_squeezingLogShear_eq_four_mul_abs` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L179 [advisory] `local-hypothesis-injection` in `theorem abs_squeezingLogShear_le_of_topologicalBekensteinBound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

