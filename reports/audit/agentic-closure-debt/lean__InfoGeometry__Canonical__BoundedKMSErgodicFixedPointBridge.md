# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:45.703697+00:00`
Root: `lean/InfoGeometry/Canonical/BoundedKMSErgodicFixedPointBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **11**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BoundedKMSErgodicFixedPointBridge.lean` | `advisory` | 29 | 0 | 11 | 7 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/BoundedKMSErgodicFixedPointBridge.lean`
- module: `InfoGeometry.Canonical.BoundedKMSErgodicFixedPointBridge`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L59 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.kms` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.ergodicMean` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.renorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.ergodicMean_modularFixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.ergodicMean_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.renorm_preserves_modularFixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.renorm_ergodicMean_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.centralizerLike` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L91 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.modularFixed_mem_centralizerLike` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field BoundedKMSErgodicFixedPointBridge.ergodicMean_regularSupportStable` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L105 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L144 [advisory] `bridge-shaped-declaration` in `theorem ergodicMean_idempotent_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L150 [advisory] `bridge-shaped-declaration` in `theorem renorm_preserves_modularFixed_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L171 [advisory] `bridge-shaped-declaration` in `theorem modularFixed_mem_centralizerLike_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L185 [advisory] `bridge-shaped-declaration` in `theorem ergodicMean_regularSupportStable_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

