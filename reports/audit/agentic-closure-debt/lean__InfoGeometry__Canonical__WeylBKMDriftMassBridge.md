# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.080536+00:00`
Root: `lean/InfoGeometry/Canonical/WeylBKMDriftMassBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylBKMDriftMassBridge.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylBKMDriftMassBridge.lean`
- module: `InfoGeometry.Canonical.WeylBKMDriftMassBridge`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `law-field-locker` in `structure-field WeylBKMDriftMassCarrier.driftIntensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field WeylBKMDriftMassCarrier.gaugeScale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field WeylBKMDriftMassCarrier.modularMassUnit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field WeylBKMDriftMassCarrier.weylParameter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field WeylBKMDriftMassCarrier.physicalMass` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L118 [soft] `skeletal-proof` in `theorem driftIntensity_apply` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `skeletal-proof` in `theorem gaugeScale_apply` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem modularMassUnit_apply` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `theorem weylParameter_apply` — proof appears to close via minimal tactic one-liner
  - L134 [soft] `skeletal-proof` in `theorem physicalMass_apply` — proof appears to close via minimal tactic one-liner
  - L192 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L195 [soft] `skeletal-proof` in `theorem metric_apply` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem mass_apply` — proof appears to close via minimal tactic one-liner

