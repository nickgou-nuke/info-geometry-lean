# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:10.051775+00:00`
Root: `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **6**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean` | `advisory` | 16 | 0 | 6 | 4 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/GeneralizedMetricRecompositionBridge.lean`
- module: `InfoGeometry.Canonical.GeneralizedMetricRecompositionBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.plusMetricTransportLift_fixed_by_minusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [advisory] `local-hypothesis-injection` in `def PolarizedRecompositionData.minusMetricTransportLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.minusMetricTransportLift_fixed_by_plusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [advisory] `local-hypothesis-injection` in `def PolarizedRecompositionData.minusMetricTransportLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.generalizedMetricTwistShadow_eq_couplingLogDefect` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.generalizedMetricPotentialShadow_eq_couplingPotentialDefect` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedLogDensity_eq_commonCarrier_add_generalizedMetricTwistShadow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L164 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.recomposedModularPotential_eq_commonCarrier_add_generalizedMetricPotentialShadow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

