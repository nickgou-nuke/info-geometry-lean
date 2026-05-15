# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.086448+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauGWCountOTBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauGWCountOTBridge.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauGWCountOTBridge.lean`
- module: `InfoGeometry.Canonical.SouriauGWCountOTBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `law-field-locker` in `structure-field SouriauGWCountOTCalibration.stateIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field SouriauGWCountOTCalibration.densityIndex` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field SouriauGWCountOTCalibration.K_beta_eq_projectiveHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field SouriauGWCountOTCalibration.expectation_eq_projectiveHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [advisory] `bridge-shaped-declaration` in `theorem gwCount_freeEnergy_and_flow_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

