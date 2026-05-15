# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:59.010665+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **31**
- Hard: **0**
- Soft: **19**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean` | `advisory` | 50 | 0 | 19 | 12 | 31 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauTomitaModularFlowBridge.lean`
- module: `InfoGeometry.Canonical.SouriauTomitaModularFlowBridge`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L44 [soft] `law-field-locker` in `structure-field SouriauTomitaLogContext.souriauMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L47 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L57 [soft] `skeletal-proof` in `theorem tomita_deltaLog_eq_thermalGenerator` — proof appears to close via minimal tactic one-liner
  - L124 [soft] `skeletal-proof` in `theorem toStandardFormCarrier_Delta_eq_modularHamiltonian` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `theorem toStandardFormCarrier_modularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L202 [soft] `law-field-locker` in `structure-field MatchedCarrierOwner.logContext` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L205 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L262 [advisory] `bridge-shaped-declaration` in `theorem matchedCarrier_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L303 [soft] `skeletal-proof` in `theorem modularHamiltonian_zero_ofZeroThermalMoment` — proof appears to close via minimal tactic one-liner
  - L321 [soft] `law-field-locker` in `structure-field SouriauTomitaKMSContext.logContext` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field SouriauTomitaKMSContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L324 [soft] `law-field-locker` in `structure-field SouriauTomitaKMSContext.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field SouriauTomitaKMSContext.kms_state_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [advisory] `existential-packaging` in `theorem mk_of_state_kms` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L347 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L347 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L397 [advisory] `bridge-shaped-declaration` in `theorem constructive_kms_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L422 [soft] `law-field-locker` in `structure-field MinimalSouriauTomitaKMSContext.logContext` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field MinimalSouriauTomitaKMSContext.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L427 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L475 [advisory] `bridge-shaped-declaration` in `theorem constructive_kms_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L502 [soft] `law-field-locker` in `structure-field CyclicSouriauTomitaKMSContext.state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L505 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L505 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L539 [soft] `skeletal-proof` in `theorem sigma_apply_eq_self` — proof appears to close via minimal tactic one-liner
  - L589 [advisory] `bridge-shaped-declaration` in `theorem constructive_kms_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

