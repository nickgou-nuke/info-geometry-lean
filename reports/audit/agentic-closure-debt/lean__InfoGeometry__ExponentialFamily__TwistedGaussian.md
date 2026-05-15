# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:30.390738+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean`
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
| `lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean` | `advisory` | 14 | 0 | 6 | 2 | 8 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/TwistedGaussian.lean`
- module: `InfoGeometry.ExponentialFamily.TwistedGaussian`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `law-field-locker` in `structure-field TwistedGaussianFamily.T` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `law-field-locker` in `structure-field TwistedGaussianFamily.T_antisymm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field TwistedGaussianFamily.normal_commutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L33 [soft] `skeletal-proof` in `theorem adjoint_T_eq_neg` — proof appears to close via minimal tactic one-liner
  - L44 [soft] `skeletal-proof` in `theorem adjoint_infoOperator` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `skeletal-proof` in `theorem normal_iff_commutes` — proof appears to close via minimal tactic one-liner

