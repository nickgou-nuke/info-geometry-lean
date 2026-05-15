# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:19.803505+00:00`
Root: `lean/InfoGeometry/Canonical/IncompressibleCramerRaoActionBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **6**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IncompressibleCramerRaoActionBridge.lean` | `advisory` | 21 | 0 | 6 | 9 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/IncompressibleCramerRaoActionBridge.lean`
- module: `InfoGeometry.Canonical.IncompressibleCramerRaoActionBridge`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L76 [soft] `skeletal-proof` in `theorem souriauFisherMetricOperator_eq_cramerRaoMetricOp` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `law-field-locker` in `structure-field CramerRaoNegLogVolumeAnomalyReadout.chiralScale_eq_metricVolumePotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `skeletal-proof` in `theorem chiralScale_eq_zero_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L109 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L115 [advisory] `local-hypothesis-injection` in `theorem chiralScale_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `skeletal-proof` in `theorem normalInference_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `local-hypothesis-injection` in `theorem normalInference_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L147 [soft] `skeletal-proof` in `theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume` — proof appears to close via minimal tactic one-liner
  - L227 [soft] `skeletal-proof` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible` — proof appears to close via minimal tactic one-liner
  - L234 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L241 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L244 [advisory] `local-hypothesis-injection` in `theorem projectorObstruction_eq_zero_and_dilationCommutator_eq_zero_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L272 [advisory] `local-hypothesis-injection` in `theorem semanticCollapsePacket_of_incompressible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

