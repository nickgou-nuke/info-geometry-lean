# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:11.619893+00:00`
Root: `lean/InfoGeometry/Canonical/WeylFiveGradeBalanceBridge.lean`
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
| `lean/InfoGeometry/Canonical/WeylFiveGradeBalanceBridge.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylFiveGradeBalanceBridge.lean`
- module: `InfoGeometry.Canonical.WeylFiveGradeBalanceBridge`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `skeletal-proof` in `theorem posTwo_negTwo_balanced` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `theorem negTwo_posTwo_balanced` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `theorem posOne_negOne_balanced` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem negOne_posOne_balanced` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `skeletal-proof` in `theorem zero_zero_balanced` — proof appears to close via minimal tactic one-liner
  - L99 [soft] `law-field-locker` in `structure-field WeylFiveGradeAssignment.grade` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L107 [soft] `skeletal-proof` in `theorem grade_apply` — proof appears to close via minimal tactic one-liner
  - L131 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L134 [soft] `skeletal-proof` in `theorem grading_apply` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `law-field-locker` in `structure-field TomitaCentralBalanceCarrier.sourceCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L186 [soft] `law-field-locker` in `structure-field TomitaCentralBalanceCarrier.sinkCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field TomitaCentralBalanceCarrier.totalCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L209 [soft] `skeletal-proof` in `theorem sourceCharge_apply` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `skeletal-proof` in `theorem sinkCharge_apply` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `theorem totalCharge_apply` — proof appears to close via minimal tactic one-liner

