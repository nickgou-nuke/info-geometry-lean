# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.045385+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinGreenHorizonEnvelope.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **6**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinGreenHorizonEnvelope.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinGreenHorizonEnvelope.lean`
- module: `InfoGeometry.Canonical.DrazinGreenHorizonEnvelope`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [soft] `law-field-locker` in `structure-field DrazinGreenData.P_reg_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field DrazinGreenData.P_harm_def` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field DrazinGreenData.P_reg_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field DrazinGreenData.P_harm_self_adjoint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L119 [soft] `skeletal-proof` in `theorem matterSupport_idempotent` — proof appears to close via minimal tactic one-liner
  - L156 [soft] `skeletal-proof` in `theorem envelope_eq_combined_support_compression` — proof appears to close via minimal tactic one-liner

