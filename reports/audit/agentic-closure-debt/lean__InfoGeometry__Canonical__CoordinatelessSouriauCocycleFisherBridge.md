# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:56.896761+00:00`
Root: `lean/InfoGeometry/Canonical/CoordinatelessSouriauCocycleFisherBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **16**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CoordinatelessSouriauCocycleFisherBridge.lean` | `advisory` | 38 | 0 | 16 | 6 | 22 |

## Findings by file

### `lean/InfoGeometry/Canonical/CoordinatelessSouriauCocycleFisherBridge.lean`
- module: `InfoGeometry.Canonical.CoordinatelessSouriauCocycleFisherBridge`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `law-field-locker` in `structure-field SouriauMomentTwoCocycle.cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [soft] `law-field-locker` in `structure-field SouriauMomentTwoCocycle.centralCorrection` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field SouriauMomentTwoCocycle.antisymmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field SouriauMomentTwoCocycle.closed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field SouriauMomentTwoCocycle.moment_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `skeletal-proof` in `theorem correctedMomentOperator_eq_moment_of_zero_correction` — proof appears to close via minimal tactic one-liner
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L114 [soft] `law-field-locker` in `structure-field CocycleFisherCorrection.base` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L115 [soft] `law-field-locker` in `structure-field CocycleFisherCorrection.correction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field CocycleFisherCorrection.correction_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `law-field-locker` in `structure-field CocycleFisherCorrection.correction_nonnegative_on_diagonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L122 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L131 [soft] `skeletal-proof` in `theorem correctedMetric_eq_base_add_correction` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `skeletal-proof` in `theorem correctedMetric_eq_base_of_correction_zero` — proof appears to close via minimal tactic one-liner
  - L174 [advisory] `existential-packaging` in `structure FiniteSouriauFisherCocycleCorrection` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L184 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L184 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L201 [soft] `skeletal-proof` in `theorem correctedResponse_betaBeta` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `skeletal-proof` in `theorem correctedResponse_symmetric` — proof appears to close via minimal tactic one-liner

