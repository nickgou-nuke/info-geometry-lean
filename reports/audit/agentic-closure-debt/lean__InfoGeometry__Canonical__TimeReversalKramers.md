# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:05.842835+00:00`
Root: `lean/InfoGeometry/Canonical/TimeReversalKramers.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **7**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TimeReversalKramers.lean` | `advisory` | 19 | 0 | 7 | 5 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/TimeReversalKramers.lean`
- module: `InfoGeometry.Canonical.TimeReversalKramers`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [soft] `law-field-locker` in `structure-field RealTimeReversal.kreinIsometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field RealTimeReversal.phaseAntilinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L43 [soft] `section-law-variable` in `variable R` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L101 [soft] `law-field-locker` in `structure-field KramersTimeReversal.square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L104 [soft] `section-law-variable` in `variable R` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L117 [soft] `skeletal-proof` in `theorem partner_ne_self_of_ne_zero` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem map_phasePartner_eq_neg_phasePartner_map` — proof appears to close via minimal tactic one-liner

