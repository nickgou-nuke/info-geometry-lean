# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:34.153042+00:00`
Root: `lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/ProjectivePrimePartition.lean`
- module: `InfoGeometry.Arithmetic.ProjectivePrimePartition`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `skeletal-proof` in `theorem projectivePrimePartition_eq_restricted` — proof appears to close via minimal tactic one-liner
  - L40 [soft] `skeletal-proof` in `theorem projectivePrimePartition_nonneg` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `law-field-locker` in `structure-field ProjectivePrimeCalibration.stateOfFinset` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field ProjectivePrimeCalibration.modularFlowReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field ProjectivePrimeCalibration.flow_eq_projectivePrimePartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

