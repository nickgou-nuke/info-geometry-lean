# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:12.879003+00:00`
Root: `lean/InfoGeometry/Canonical/WeylNormalizedCARCCRBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **42**
- Hard: **0**
- Soft: **30**
- Advisory: **12**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylNormalizedCARCCRBridge.lean` | `advisory` | 72 | 0 | 30 | 12 | 42 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylNormalizedCARCCRBridge.lean`
- module: `InfoGeometry.Canonical.WeylNormalizedCARCCRBridge`
- status: `advisory`
- debt_score: `72`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L55 [soft] `law-field-locker` in `structure-field WeylNormalizedCARCCRBridge.hodgeBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field WeylNormalizedCARCCRBridge.lambda_sq_mul_nu_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L68 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L126 [soft] `skeletal-proof` in `theorem normalizedCAR_of_raw` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `local-hypothesis-injection` in `theorem normalizedCAR_of_raw` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [soft] `skeletal-proof` in `theorem normalizedCCR_of_raw` — proof appears to close via minimal tactic one-liner
  - L176 [advisory] `local-hypothesis-injection` in `theorem normalizedCCR_of_raw` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L183 [soft] `skeletal-proof` in `theorem normalizedDiracPlus_mul_normalizedDiracPlus_eq_zero` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem normalizedDiracMinus_mul_normalizedDiracMinus_eq_zero` — proof appears to close via minimal tactic one-liner
  - L241 [soft] `law-field-locker` in `structure-field ScaledCARPair.lambda_sq_mul_nu_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L242 [soft] `law-field-locker` in `structure-field ScaledCARPair.raw_annihilation_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L244 [soft] `law-field-locker` in `structure-field ScaledCARPair.raw_creation_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field ScaledCARPair.raw_mixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L304 [advisory] `local-hypothesis-injection` in `theorem normalized_isCARPair` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L381 [soft] `law-field-locker` in `structure-field ScaledCCRPair.lambda_sq_mul_nu_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L382 [soft] `law-field-locker` in `structure-field ScaledCCRPair.raw_commutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L387 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L415 [soft] `skeletal-proof` in `theorem normalized_isCCRPair` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `theorem normalized_isCCRPair` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L431 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L443 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.hodgeBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L445 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.toFock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L454 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.lambda_sq_mul_nu_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L457 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.raw_diracPlus_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L462 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.raw_diracMinus_nil` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L467 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCARAdapter.raw_mixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L475 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L475 [soft] `section-law-variable` in `variable A` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L492 [soft] `skeletal-proof` in `theorem scaledCARPair_annihilation_eq_toFock_diracPlus` — proof appears to close via minimal tactic one-liner
  - L498 [soft] `skeletal-proof` in `theorem scaledCARPair_creation_eq_toFock_diracMinus` — proof appears to close via minimal tactic one-liner
  - L520 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCCRAdapter.hodgeBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L522 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCCRAdapter.toFock` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L531 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCCRAdapter.lambda_sq_mul_nu_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L534 [soft] `law-field-locker` in `structure-field DrazinHodgeFockCCRAdapter.raw_commutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L542 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L542 [soft] `section-law-variable` in `variable A` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L557 [soft] `skeletal-proof` in `theorem scaledCCRPair_annihilation_eq_toFock_diracMinus` — proof appears to close via minimal tactic one-liner
  - L563 [soft] `skeletal-proof` in `theorem scaledCCRPair_creation_eq_toFock_diracPlus` — proof appears to close via minimal tactic one-liner

