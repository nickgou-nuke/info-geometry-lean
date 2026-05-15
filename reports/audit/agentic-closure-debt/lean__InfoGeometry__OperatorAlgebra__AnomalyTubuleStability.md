# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.719256+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **23**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean` | `advisory` | 50 | 0 | 23 | 4 | 27 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AnomalyTubuleStability.lean`
- module: `InfoGeometry.OperatorAlgebra.AnomalyTubuleStability`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `law-field-locker` in `structure-field AnomalyReadout.symmetryVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field AnomalyReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field AnomalyReadout.nonvanishingCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L51 [soft] `skeletal-proof` in `theorem anomaly_eq_readout_variation` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.anomaly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.flatFrame` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.flat_anomaly_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.defect_flow_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `law-field-locker` in `structure-field AnomalousFlowWitness.anomaly_detects_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L132 [soft] `law-field-locker` in `structure-field ChiralAnomalyDatum.backend` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field ChiralAnomalyDatum.cyclicCocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field ChiralAnomalyDatum.anomalyCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field WeylAnomalyDatum.conformalVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L159 [soft] `law-field-locker` in `structure-field WeylAnomalyDatum.zetaResidue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field WeylAnomalyDatum.anomalyCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field DIIIInteractionInvariant.reduction_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field CliffordToDIIIInteractionBridge.compatibility` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [soft] `law-field-locker` in `structure-field TubuleStabilityDatum.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field TubuleStabilityDatum.sectorReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [soft] `law-field-locker` in `structure-field TubuleStabilityDatum.isNontrivialSector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L232 [soft] `law-field-locker` in `structure-field TubuleStabilityDatum.stableNontrivialSector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

