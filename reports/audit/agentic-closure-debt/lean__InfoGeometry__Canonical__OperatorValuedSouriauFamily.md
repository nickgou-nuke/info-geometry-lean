# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:37.829067+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorValuedSouriauFamily.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **13**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorValuedSouriauFamily.lean` | `advisory` | 28 | 0 | 13 | 2 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorValuedSouriauFamily.lean`
- module: `InfoGeometry.Canonical.OperatorValuedSouriauFamily`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.quantumMomentMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.eval` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.freeEnergyReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.souriauGenerator_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.expWeight_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.beta_is_operatorial_thermal_direction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.time_is_operatorial_clock_direction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.scalar_time_is_chart_parameter_only` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.scalar_beta_is_chart_shadow_only` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.duhamelDerivativeLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L112 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.scalarReadoutDownstreamOnly` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.exponentialFamily_K_beta_eq_souriauGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field OperatorValuedSouriauFamily.exponentialFamily_untraced_beta_eq_expWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

