# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:44.384694+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountProbabilityDrazinBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **4**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountProbabilityDrazinBridge.lean` | `advisory` | 17 | 0 | 4 | 9 | 13 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/ProjectiveCountProbabilityDrazinBridge.lean`
- module: `InfoGeometry.GromovWittenErlangen.ProjectiveCountProbabilityDrazinBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [advisory] `existential-packaging` in `structure GWProjectiveCountProbabilityBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L52 [soft] `law-field-locker` in `structure-field GWProjectiveCountProbabilityBridge.probabilityGaugeLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [advisory] `witness-field-projection` in `structure-field probabilityGauge_valid` — witness field `probabilityGauge_valid : probabilityGaugeLaw` detected; verify owner-level derivation
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L144 [advisory] `existential-packaging` in `structure GWProjectiveCountDrazinBridge` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L154 [soft] `law-field-locker` in `structure-field GWProjectiveCountDrazinBridge.localization_packet_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L162 [soft] `law-field-locker` in `structure-field GWProjectiveCountDrazinBridge.edgeEulerWeight_eq_projectiveCountReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [advisory] `witness-field-projection` in `structure-field edgeEulerWeight_eq_projectiveCountReadout_valid` — witness field `edgeEulerWeight_eq_projectiveCountReadout_valid : edgeEulerWeight_eq_projectiveCountReadout` detected; verify owner-level derivation
  - L173 [soft] `law-field-locker` in `structure-field GWProjectiveCountDrazinBridge.drazinResidue_eq_projectiveSingularityReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `witness-field-projection` in `structure-field drazinResidue_eq_projectiveSingularityReadout_valid` — witness field `drazinResidue_eq_projectiveSingularityReadout_valid : drazinResidue_eq_projectiveSingularityReadout` detected; verify owner-level derivation
  - L189 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L200 [advisory] `bridge-shaped-declaration` in `theorem localization_packet_matches_projectiveCounts` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

