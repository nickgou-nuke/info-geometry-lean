# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:43.956534+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **12**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountBridge.lean` | `advisory` | 31 | 0 | 12 | 7 | 19 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountBridge.lean`
- module: `InfoGeometry.GromovWittenErlangen.ProjectiveCountBridge`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field GWProjectiveCountState.vertexCode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field GWProjectiveCountState.edgeCode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field GWProjectiveCountState.coeffReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field GWProjectiveCountState.countShadowLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [advisory] `witness-field-projection` in `structure-field countShadow_valid` — witness field `countShadow_valid : countShadowLaw` detected; verify owner-level derivation
  - L75 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L95 [soft] `skeletal-proof` in `theorem normalizedShape_scale_counts` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `skeletal-proof` in `theorem normalizedShape_scale_counts_apply` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem normalizedShape_eq_of_samePositiveRay` — proof appears to close via minimal tactic one-liner
  - L133 [soft] `skeletal-proof` in `theorem normalizedShape_sum_eq_one` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `law-field-locker` in `structure-field ProjectiveCountVolumeGauge.volume_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field ProjectiveCountVolumeGauge.kB_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L171 [soft] `law-field-locker` in `structure-field ProjectiveCountVolumeGauge.entropy_eq_kB_log_volume` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L175 [soft] `law-field-locker` in `structure-field ProjectiveCountVolumeGauge.volumeGaugeLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [advisory] `witness-field-projection` in `structure-field volumeGauge_valid` — witness field `volumeGauge_valid : volumeGaugeLaw` detected; verify owner-level derivation
  - L186 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L223 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L257 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

