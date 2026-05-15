# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.854477+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinLightConeDictionary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **15**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinLightConeDictionary.lean` | `advisory` | 41 | 0 | 15 | 11 | 26 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinLightConeDictionary.lean`
- module: `InfoGeometry.Canonical.DrazinLightConeDictionary`
- status: `advisory`
- debt_score: `41`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `law-field-locker` in `structure-field ProjectorSplit.P_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field ProjectorSplit.P0_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `law-field-locker` in `structure-field ProjectorSplit.P_add_P0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field ProjectorSplit.P_mul_P0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field ProjectorSplit.P0_mul_P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L84 [soft] `skeletal-proof` in `theorem commutator_P_eq_uPlus_sub_uMinus` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem chiralGrading_mul_uPlus` — proof appears to close via minimal tactic one-liner
  - L130 [advisory] `local-hypothesis-injection` in `theorem chiralGrading_mul_uPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L132 [advisory] `local-hypothesis-injection` in `theorem chiralGrading_mul_uPlus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [soft] `skeletal-proof` in `theorem uPlus_mul_chiralGrading` — proof appears to close via minimal tactic one-liner
  - L141 [advisory] `local-hypothesis-injection` in `theorem uPlus_mul_chiralGrading` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L143 [advisory] `local-hypothesis-injection` in `theorem uPlus_mul_chiralGrading` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [soft] `skeletal-proof` in `theorem chiralGrading_mul_uMinus` — proof appears to close via minimal tactic one-liner
  - L152 [advisory] `local-hypothesis-injection` in `theorem chiralGrading_mul_uMinus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L154 [advisory] `local-hypothesis-injection` in `theorem chiralGrading_mul_uMinus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L160 [soft] `skeletal-proof` in `theorem uMinus_mul_chiralGrading` — proof appears to close via minimal tactic one-liner
  - L163 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_chiralGrading` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `theorem uMinus_mul_chiralGrading` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L217 [soft] `law-field-locker` in `structure-field DrazinMPHorizonDatum.PR_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L218 [soft] `law-field-locker` in `structure-field DrazinMPHorizonDatum.PL_idem` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field DrazinMPHorizonDatum.chiR_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field DrazinMPHorizonDatum.chiL_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field DrazinMPHorizonDatum.Q_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L229 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

