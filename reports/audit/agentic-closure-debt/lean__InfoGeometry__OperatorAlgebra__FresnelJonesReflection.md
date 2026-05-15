# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:14.771406+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FresnelJonesReflection.lean`
- module: `InfoGeometry.OperatorAlgebra.FresnelJonesReflection`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L155 [soft] `skeletal-proof` in `theorem fresnelRP_eq_zero_of_num_zero` — proof appears to close via minimal tactic one-liner
  - L174 [soft] `law-field-locker` in `structure-field TotalInternalReflectionDatum.r_s_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field TotalInternalReflectionDatum.r_p_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `skeletal-proof` in `theorem circularReflection_brewster_apply_left` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `theorem circularReflection_brewster_apply_right` — proof appears to close via minimal tactic one-liner
  - L257 [soft] `law-field-locker` in `structure-field AnisotropicReflectionDatum.jones` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L268 [soft] `law-field-locker` in `structure-field RoughReflectionChannelDatum.channel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field RoughReflectionChannelDatum.depolarizingCertificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L274 [soft] `law-field-locker` in `structure-field RoughReflectionChannelDatum.directionDependentIncidencePlanes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

