# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:42.210890+00:00`
Root: `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/PhaseSpaceRecompositionBridge.lean`
- module: `InfoGeometry.Canonical.PhaseSpaceRecompositionBridge`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [advisory] `existential-packaging` in `def PolarizedRecompositionData.minusPhaseTransportLift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.plusPhaseTransportLift_realizes_as_plusMetricTransportLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.minusPhaseTransportLift_realizes_as_minusMetricTransportLift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.plusPhaseTransportLift_fixed_by_phaseMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_generalizedMetric_minusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.plusPhaseTransportLift_realize_fixed_by_realizedMinusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L255 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.minusPhaseTransportLift_fixed_by_phasePlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L301 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_generalizedMetric_plusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L348 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.minusPhaseTransportLift_realize_fixed_by_realizedPlusProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L616 [soft] `simp-law-injection` in `simp-declaration PolarizedRecompositionData.phaseTransport_descends_to_generalizedMetricTwistShadow` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

