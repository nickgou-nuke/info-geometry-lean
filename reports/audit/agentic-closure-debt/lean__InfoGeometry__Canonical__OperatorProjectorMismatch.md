# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:36.998807+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorProjectorMismatch.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorProjectorMismatch.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorProjectorMismatch.lean`
- module: `InfoGeometry.Canonical.OperatorProjectorMismatch`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `law-field-locker` in `structure-field ProjectorPair.PD_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [soft] `law-field-locker` in `structure-field ProjectorPair.PMP_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [advisory] `local-hypothesis-injection` in `theorem projectorAgreement_implies_commutator_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `theorem commutator_ne_zero_implies_mismatch_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L119 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PD0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PDtimes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PMP0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PMPtimes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PD0_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field DrazinMPProjectorData.PMP0_idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

