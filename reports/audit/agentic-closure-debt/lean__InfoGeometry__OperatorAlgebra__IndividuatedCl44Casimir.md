# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:15.931462+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/IndividuatedCl44Casimir.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/IndividuatedCl44Casimir.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/IndividuatedCl44Casimir.lean`
- module: `InfoGeometry.OperatorAlgebra.IndividuatedCl44Casimir`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `law-field-locker` in `structure-field DiracSouriauCoreTrace.scalarTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field DiracSouriauCoreTrace.pseudoscalarTrace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L91 [soft] `skeletal-proof` in `theorem constructCasimirCandidate_eq_trace_sum` — proof appears to close via minimal tactic one-liner
  - L123 [soft] `skeletal-proof` in `theorem diracSouriauCasimir_eq_trace_identity` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `law-field-locker` in `structure-field PfaffianCasimirCalibration.pfaffian_eq_constructCasimirCandidate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

