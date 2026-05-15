# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:42.060657+00:00`
Root: `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **12**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean` | `advisory` | 28 | 0 | 12 | 4 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/PhaseSpacePolarizedBridge.lean`
- module: `InfoGeometry.Canonical.PhaseSpacePolarizedBridge`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L55 [advisory] `existential-packaging` in `def MinusRestrictedRelativeModularData.phaseLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L59 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.realize_phaseLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.realize_phaseLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.phaseLift_fixed_by_phasePlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [advisory] `local-hypothesis-injection` in `def MinusRestrictedRelativeModularData.phaseLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_plusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration PlusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.phaseLift_fixed_by_phaseMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L194 [advisory] `local-hypothesis-injection` in `def MinusRestrictedRelativeModularData.phaseLift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_generalizedMetric_minusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L261 [soft] `simp-law-injection` in `simp-declaration MinusRestrictedRelativeModularData.realize_phaseLift_fixed_by_realizedMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L295 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.plus_realize_phaseLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L302 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.minus_realize_phaseLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L309 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.plus_phaseLift_fixed_by_phasePlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L316 [soft] `simp-law-injection` in `simp-declaration PolarizedRelativeModularPair.minus_phaseLift_fixed_by_phaseMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

