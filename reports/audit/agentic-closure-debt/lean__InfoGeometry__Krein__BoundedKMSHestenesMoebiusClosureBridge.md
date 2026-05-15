# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:49.041049+00:00`
Root: `lean/InfoGeometry/Krein/BoundedKMSHestenesMoebiusClosureBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/BoundedKMSHestenesMoebiusClosureBridge.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/Krein/BoundedKMSHestenesMoebiusClosureBridge.lean`
- module: `InfoGeometry.Krein.BoundedKMSHestenesMoebiusClosureBridge`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L60 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.boundedWilson` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.vectorAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.vectorAction_krein_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.vectorAction_fixes_omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.operatorAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.operatorAction_phaseAxis_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L87 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.volumeState_operatorAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.wordAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.atomExpectation_wordAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.wilsonHolonomy_wordAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field BoundedKMSHestenesMoebiusClosureBridge.moebius_closure_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `skeletal-proof` in `theorem moebius_wilson_eq` — proof appears to close via minimal tactic one-liner

