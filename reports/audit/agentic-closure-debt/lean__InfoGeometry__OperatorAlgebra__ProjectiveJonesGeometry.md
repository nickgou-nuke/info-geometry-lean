# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:20.844252+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ProjectiveJonesGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **9**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ProjectiveJonesGeometry.lean` | `advisory` | 21 | 0 | 9 | 3 | 12 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ProjectiveJonesGeometry.lean`
- module: `InfoGeometry.OperatorAlgebra.ProjectiveJonesGeometry`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L42 [soft] `simp-law-injection` in `simp-declaration act_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `skeletal-proof` in `theorem act_one` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `law-field-locker` in `structure-field JonesCartanAxis.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field JonesCartanAxis.P_left_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field JonesCartanAxis.P_right_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L81 [soft] `law-field-locker` in `structure-field JonesCartanAxis.complementary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L85 [soft] `law-field-locker` in `structure-field JonesCartanAxis.left_right_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field JonesCartanAxis.right_left_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field OperatorialJonesCalculus.preserves_axis` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

