# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:51.651245+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **15**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean` | `advisory` | 34 | 0 | 15 | 4 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularRecomposition.lean`
- module: `InfoGeometry.Canonical.RelativeModularRecomposition`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `existential-packaging` in `structure PolarizedRecompositionData` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L47 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.carrier_eq_plus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.carrier_eq_minus` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.couplingPotentialDefect_eq_neg_couplingLogDefect` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [advisory] `existential-packaging` in `def PolarizedRecompositionData.exactPotentialRecomposition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L156 [soft] `classical-witness-smuggling` in `def PolarizedRecompositionData.exactPotentialRecomposition` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L161 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedAmbientLogDensity_eq_commonCarrier` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedAmbientModularPotential_eq_commonCarrier` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedLogDensity_eq_ambient_add_coupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L213 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_coupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L222 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_ambient_add_coupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_coupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L249 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_neg_recomposedLogDensity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L281 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_vanishingCoupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L291 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_vanishingCoupling` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L320 [advisory] `local-hypothesis-injection` in `def PolarizedRecompositionData.exactPotentialRecomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L381 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_of_sectorwiseExact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L405 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_of_sectorwiseExact` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

