# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:41.988155+00:00`
Root: `lean/InfoGeometry/GromovHomologicalProbabilityRoadmap.lean`
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
| `lean/InfoGeometry/GromovHomologicalProbabilityRoadmap.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/GromovHomologicalProbabilityRoadmap.lean`
- module: `InfoGeometry.GromovHomologicalProbabilityRoadmap`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `law-field-locker` in `structure-field MomentumMapProbabilityPacket.momentumMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L29 [soft] `law-field-locker` in `structure-field MomentumMapProbabilityPacket.momentumValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.observableMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field HomologicalMeasurePacket.supportIdeal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field WeylVolumeGaugePacket.volumeGauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field WeylVolumeGaugePacket.spectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field GromovHomologicalProbabilityRoadmapPacket.stateToHomological` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field GromovHomologicalProbabilityRoadmapPacket.stateToCycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field GromovHomologicalProbabilityRoadmapPacket.volume_consistency` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [advisory] `existential-packaging` in `def GromovHomologicalProbabilityRoadmapTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

