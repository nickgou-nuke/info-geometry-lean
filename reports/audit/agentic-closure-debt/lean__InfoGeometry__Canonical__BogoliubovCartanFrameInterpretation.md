# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.049808+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **18**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean` | `advisory` | 39 | 0 | 18 | 3 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovCartanFrameInterpretation.lean`
- module: `InfoGeometry.Canonical.BogoliubovCartanFrameInterpretation`
- status: `advisory`
- debt_score: `39`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `skeletal-proof` in `theorem bogoliubovFrameAction_eq_conjugate` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `theorem cartanInvolution_is_neutralJ_conjugation` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `skeletal-proof` in `theorem cartanInvolutionGroup_is_modular_j_orthogonal` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `law-field-locker` in `structure-field BogoliubovKANFrame.kan_factorization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L119 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L135 [soft] `simp-law-injection` in `simp-declaration frameAction_eq_frame_conjugation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration diagonalOperatorReadout_eq_Apart_conjugation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `skeletal-proof` in `theorem frame_eq_KAN` — proof appears to close via minimal tactic one-liner
  - L152 [soft] `simp-law-injection` in `simp-declaration frameAction_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L158 [soft] `simp-law-injection` in `simp-declaration diagonalOperatorReadout_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L188 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.operator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L190 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.frame` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L192 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.framedOperator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L194 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.diagonalReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.framedOperator_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field OperatorInBogoliubovKANChart.diagonalReadout_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L202 [soft] `section-law-variable` in `variable O` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L204 [soft] `skeletal-proof` in `theorem primitive_operator_owner` — proof appears to close via minimal tactic one-liner

