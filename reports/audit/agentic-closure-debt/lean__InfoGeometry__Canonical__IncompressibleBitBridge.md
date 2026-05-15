# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:19.655475+00:00`
Root: `lean/InfoGeometry/Canonical/IncompressibleBitBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IncompressibleBitBridge.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/IncompressibleBitBridge.lean`
- module: `InfoGeometry.Canonical.IncompressibleBitBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field UnitRelativeVolumeBit.unit_relative_volume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `skeletal-proof` in `theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume` — proof appears to close via minimal tactic one-liner
  - L251 [advisory] `local-hypothesis-injection` in `theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L270 [advisory] `local-hypothesis-injection` in `theorem isNormalInference_of_incompressibleBit_of_chiralScale_eq_cramerRaoVolumePotential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L358 [soft] `skeletal-proof` in `theorem not_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume_of_unitOfAction_ne_zero` — proof appears to close via minimal tactic one-liner
  - L367 [advisory] `local-hypothesis-injection` in `theorem not_incompressibleBit_of_chiralScale_eq_neg_cramerRaoLogVolume_of_unitOfAction_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

