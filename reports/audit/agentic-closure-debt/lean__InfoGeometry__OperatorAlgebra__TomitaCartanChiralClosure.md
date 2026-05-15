# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:24.907639+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/TomitaCartanChiralClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/TomitaCartanChiralClosure.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/TomitaCartanChiralClosure.lean`
- module: `InfoGeometry.OperatorAlgebra.TomitaCartanChiralClosure`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field TomitaCartanChiralKreinDynamics.boundary_eq_J_conj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L91 [soft] `skeletal-proof` in `theorem noncompact_left_supported_hit_is_right_supported` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem noncompact_right_supported_hit_is_left_supported` — proof appears to close via minimal tactic one-liner

