# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:58.445183+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauSurprisalKLFreeEnergyBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauSurprisalKLFreeEnergyBridge.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauSurprisalKLFreeEnergyBridge.lean`
- module: `InfoGeometry.Canonical.SouriauSurprisalKLFreeEnergyBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L145 [soft] `law-field-locker` in `structure-field SouriauThermodynamicCarrier.surprisal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L147 [soft] `law-field-locker` in `structure-field SouriauThermodynamicCarrier.relativeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `law-field-locker` in `structure-field SouriauThermodynamicCarrier.souriauBeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field SouriauThermodynamicCarrier.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L153 [soft] `law-field-locker` in `structure-field SouriauThermodynamicCarrier.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field ScalarThermalGauge.inverseTemperature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L225 [soft] `law-field-locker` in `structure-field ModularFreeEnergyReadout.modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

