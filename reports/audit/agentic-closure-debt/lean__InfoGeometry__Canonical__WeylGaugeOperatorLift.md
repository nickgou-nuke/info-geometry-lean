# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:12.113145+00:00`
Root: `lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **23**
- Hard: **0**
- Soft: **16**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean` | `advisory` | 39 | 0 | 16 | 7 | 23 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylGaugeOperatorLift.lean`
- module: `InfoGeometry.Canonical.WeylGaugeOperatorLift`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L41 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `simp-law-injection` in `simp-declaration plusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration minusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration plusToMinusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration minusToPlusBlockMap_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L80 [soft] `simp-law-injection` in `simp-declaration plusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration minusProjectorFlux_liftedOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [advisory] `local-hypothesis-injection` in `theorem liftedOperator_mulTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [soft] `simp-law-injection` in `simp-declaration logarithmicGenerator_eq_common_plus_relative_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L146 [soft] `simp-law-injection` in `simp-declaration relativeVolumeScale_eq_abs_character` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [soft] `simp-law-injection` in `simp-declaration determinantCharacter_gaugeRescale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L162 [soft] `simp-law-injection` in `simp-declaration relativeVolumeScale_gaugeRescale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L169 [soft] `simp-law-injection` in `simp-declaration determinantCharacter_mulTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L186 [soft] `simp-law-injection` in `simp-declaration relativeVolumeScale_mulTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L253 [soft] `simp-law-injection` in `simp-declaration liftedOperator_referenceTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L258 [advisory] `local-hypothesis-injection` in `def relativeDilationTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L267 [soft] `simp-law-injection` in `simp-declaration liftedOperator_isotropicGaugeTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L273 [soft] `simp-law-injection` in `simp-declaration liftedOperator_relativeDilationTransport` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L288 [advisory] `local-hypothesis-injection` in `theorem liftedOperator_referenceTransport_eq_gauge_smul_epsilonBoost` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L293 [advisory] `local-hypothesis-injection` in `theorem liftedOperator_referenceTransport_eq_gauge_smul_epsilonBoost` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [soft] `skeletal-proof` in `theorem isotropicGaugeTransport_commutes_relativeDilationTransport` — proof appears to close via minimal tactic one-liner

