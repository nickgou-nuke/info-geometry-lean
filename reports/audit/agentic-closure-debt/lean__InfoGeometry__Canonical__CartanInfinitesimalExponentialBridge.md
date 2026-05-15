# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:48.792946+00:00`
Root: `lean/InfoGeometry/Canonical/CartanInfinitesimalExponentialBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **10**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CartanInfinitesimalExponentialBridge.lean` | `advisory` | 29 | 0 | 10 | 9 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/CartanInfinitesimalExponentialBridge.lean`
- module: `InfoGeometry.Canonical.CartanInfinitesimalExponentialBridge`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [advisory] `bridge-shaped-declaration` in `theorem cartanEigenOperator_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L53 [soft] `skeletal-proof` in `theorem cartanAdjoint_self_zero` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `skeletal-proof` in `theorem cartanEigenOperator_conjugate` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `law-field-locker` in `structure-field ExponentialEigenFlow.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field ExponentialEigenFlow.flow_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L119 [soft] `section-law-variable` in `variable F` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L131 [soft] `skeletal-proof` in `theorem flow_add_on_eigenvector` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `law-field-locker` in `structure-field CartanEigenAdjointExponentialCalibration.expH` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [soft] `law-field-locker` in `structure-field CartanEigenAdjointExponentialCalibration.expNegH` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L183 [soft] `law-field-locker` in `structure-field CartanEigenAdjointExponentialCalibration.exponential_adjoint_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L188 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L193 [advisory] `bridge-shaped-declaration` in `theorem infinitesimal_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L199 [advisory] `bridge-shaped-declaration` in `theorem exponential_adjoint_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L206 [advisory] `bridge-shaped-declaration` in `theorem exponential_zero_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L223 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L225 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

