# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:41.699183+00:00`
Root: `lean/InfoGeometry/Canonical/BKMDriftMetric.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **14**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BKMDriftMetric.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/BKMDriftMetric.lean`
- module: `InfoGeometry.Canonical.BKMDriftMetric`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L47 [soft] `law-field-locker` in `structure-field BKMDriftMetricCarrier.scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field BKMDriftMetricCarrier.driftIntensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field BKMDriftMetricCarrier.gaugeScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field BKMDriftMetricCarrier.physicalMass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L89 [soft] `skeletal-proof` in `theorem driftIntensity_apply` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem gaugeScale_apply` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem physicalMass_apply` — proof appears to close via minimal tactic one-liner
  - L144 [soft] `law-field-locker` in `structure-field ConnesBKMDriftFusion.stateWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L145 [soft] `law-field-locker` in `structure-field ConnesBKMDriftFusion.tangentDrift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L168 [soft] `skeletal-proof` in `theorem bkm_apply` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `theorem metric_apply` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `law-field-locker` in `structure-field OperatorBKMDriftFusion.driftGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L230 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L233 [soft] `skeletal-proof` in `theorem bkmHessian_apply` — proof appears to close via minimal tactic one-liner
  - L237 [soft] `skeletal-proof` in `theorem metric_apply` — proof appears to close via minimal tactic one-liner

