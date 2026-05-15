# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:31.245717+00:00`
Root: `lean/InfoGeometry/Applications/STUGradientFlow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Applications/STUGradientFlow.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Applications/STUGradientFlow.lean`
- module: `InfoGeometry.Applications.STUGradientFlow`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `law-field-locker` in `structure-field STUFisherMetricWitness.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field STUFisherMetricWitness.metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field STUFisherMetricWitness.inverse_metric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field STUFisherMetricWitness.inversion_cert` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field DiagonalDrazinSurgery.is_horizon` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L108 [soft] `law-field-locker` in `structure-field DiagonalDrazinSurgery.drazin_projector` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field DiagonalDrazinSurgery.post_surgery_potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

