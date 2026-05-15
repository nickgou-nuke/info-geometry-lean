# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:52.103665+00:00`
Root: `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **46**
- Hard: **0**
- Soft: **44**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativePotentialCore.lean` | `advisory` | 90 | 0 | 44 | 2 | 46 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativePotentialCore.lean`
- module: `InfoGeometry.Canonical.RelativePotentialCore`
- status: `advisory`
- debt_score: `90`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [advisory] `existential-packaging` in `def representativeModularPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L45 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_eq_log_sub_log` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration representativeRelativeDensity_eq_exp_representativeRelativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration representativeModularPotential_eq_neg_representativeRelativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration representativeRelativeDensity_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration representativeRelativeDensity_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_scale_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L113 [soft] `simp-law-injection` in `simp-declaration representativeModularPotential_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L122 [soft] `simp-law-injection` in `simp-declaration representativeModularPotential_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L131 [soft] `simp-law-injection` in `simp-declaration representativeRelativeLogDensity_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration representativeRelativeDensity_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `simp-law-injection` in `simp-declaration representativeModularPotential_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L225 [soft] `simp-law-injection` in `simp-declaration representativeMassShift_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L231 [soft] `simp-law-injection` in `simp-declaration representativeMassShift_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `simp-law-injection` in `simp-declaration representativeMassShift_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L258 [soft] `simp-law-injection` in `simp-declaration relativeDensity_mk_eq_massRatio_mul_representativeRelativeDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L280 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_mk_eq_representativeRelativeLogDensity_add_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L318 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_mk_eq_representativeModularPotential_sub_massShift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L333 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_eq_logDensity_sub_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L342 [soft] `simp-law-injection` in `simp-declaration relativeDensity_eq_exp_relativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L349 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_eq_neg_relativeLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L356 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_eq_logDensity_base_sub_logDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L358 [soft] `skeletal-proof` in `theorem relativeModularPotential_eq_logDensity_base_sub_logDensity` — proof appears to close via minimal tactic one-liner
  - L366 [soft] `simp-law-injection` in `simp-declaration gaugeSection_eq_relativeDensity_mul_gaugeSection` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L380 [soft] `simp-law-injection` in `simp-declaration relativeDensity_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L386 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L392 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L398 [soft] `simp-law-injection` in `simp-declaration informationGeometricRelativeNorm_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L411 [soft] `skeletal-proof` in `theorem informationGeometricRelativeNorm_eq_sum_gauge_abs_neg_relativeLogDensity` — proof appears to close via minimal tactic one-liner
  - L418 [soft] `simp-law-injection` in `simp-declaration relativeInformationEnergy_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L425 [soft] `simp-law-injection` in `simp-declaration relativeInformationNorm_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L449 [soft] `simp-law-injection` in `simp-declaration informationGeometricRelativeNorm_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L463 [soft] `simp-law-injection` in `simp-declaration informationGeometricRelativeNorm_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L477 [soft] `simp-law-injection` in `simp-declaration informationGeometricRelativeNorm_scale_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L488 [soft] `simp-law-injection` in `simp-declaration relativeInformationEnergy_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L502 [soft] `simp-law-injection` in `simp-declaration relativeInformationEnergy_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L516 [soft] `simp-law-injection` in `simp-declaration relativeInformationEnergy_scale_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L526 [soft] `simp-law-injection` in `simp-declaration relativeInformationNorm_scale_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L537 [soft] `simp-law-injection` in `simp-declaration relativeInformationNorm_scale_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L548 [soft] `simp-law-injection` in `simp-declaration relativeInformationNorm_scale_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L559 [soft] `simp-law-injection` in `simp-declaration relativeLogDensity_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L568 [soft] `simp-law-injection` in `simp-declaration relativeDensity_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L577 [soft] `simp-law-injection` in `simp-declaration relativeModularPotential_cocycle` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

