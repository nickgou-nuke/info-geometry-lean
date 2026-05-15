# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.572495+00:00`
Root: `lean/InfoGeometry/MaxEnt/Core.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **3**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/Core.lean` | `advisory` | 10 | 0 | 3 | 4 | 7 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/Core.lean`
- module: `InfoGeometry.MaxEnt.Core`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `law-field-locker` in `structure-field ACProbMeasure.prob` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `skeletal-proof` in `lemma coe_eq_of_measure_eq` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `law-field-locker` in `structure-field LinearConstraint.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L150 [advisory] `existential-packaging` in `def HasExponentialRNForm` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L180 [advisory] `existential-packaging` in `theorem IsMaxEntSolution.hasExponentialRNForm_of_finiteSupportDuality` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

