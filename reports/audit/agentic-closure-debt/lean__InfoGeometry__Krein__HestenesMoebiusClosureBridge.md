# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:52.667330+00:00`
Root: `lean/InfoGeometry/Krein/HestenesMoebiusClosureBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **14**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/HestenesMoebiusClosureBridge.lean` | `advisory` | 33 | 0 | 14 | 5 | 19 |

## Findings by file

### `lean/InfoGeometry/Krein/HestenesMoebiusClosureBridge.lean`
- module: `InfoGeometry.Krein.HestenesMoebiusClosureBridge`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L46 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L68 [soft] `law-field-locker` in `structure-field MoebiusParameter.det_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.wilson` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.vectorAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.vectorAction_krein_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.vectorAction_fixes_omega` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L111 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.operatorAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L114 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.operatorAction_phaseAxis_fixed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.volumeState_operatorAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.wordAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.atomExpectation_wordAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.wilsonHolonomy_wordAction_invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field HestenesMoebiusClosureBridge.moebius_closure_certificate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L150 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L220 [advisory] `local-hypothesis-injection` in `theorem moebius_preserves_hestenesAnalyticSymmetry` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L257 [soft] `skeletal-proof` in `theorem moebius_unit_vacuum_expectation` — proof appears to close via minimal tactic one-liner

