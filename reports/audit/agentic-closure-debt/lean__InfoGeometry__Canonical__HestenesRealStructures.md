# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:15.013727+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesRealStructures.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **16**
- Advisory: **14**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesRealStructures.lean` | `advisory` | 46 | 0 | 16 | 14 | 30 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesRealStructures.lean`
- module: `InfoGeometry.Canonical.HestenesRealStructures`
- status: `advisory`
- debt_score: `46`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L130 [soft] `law-field-locker` in `structure-field PhaseKramersAxis.kreinAntiIsometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L131 [soft] `law-field-locker` in `structure-field PhaseKramersAxis.phaseLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field PhaseKramersAxis.square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `law-field-locker` in `structure-field KramersSymmetry.kreinIsometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field KramersSymmetry.phaseAntilinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field KramersSymmetry.square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L154 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L170 [soft] `skeletal-proof` in `theorem anticomm_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L179 [soft] `skeletal-proof` in `theorem partner_ne_self_of_ne_zero` — proof appears to close via minimal tactic one-liner
  - L182 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L184 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L186 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L197 [advisory] `local-hypothesis-injection` in `theorem partner_ne_self_of_ne_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L209 [soft] `law-field-locker` in `structure-field MajoranaRealStructure.involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L210 [soft] `law-field-locker` in `structure-field MajoranaRealStructure.kreinIsometric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field MajoranaRealStructure.phaseLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field MajoranaRealStructure.gradingLinear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L216 [soft] `section-law-variable` in `variable M` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L231 [advisory] `local-hypothesis-injection` in `def fixedSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L232 [advisory] `local-hypothesis-injection` in `def fixedSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [advisory] `local-hypothesis-injection` in `def fixedSubmodule` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L252 [soft] `skeletal-proof` in `theorem phaseAxis_closed` — proof appears to close via minimal tactic one-liner
  - L269 [soft] `skeletal-proof` in `theorem grading_closed` — proof appears to close via minimal tactic one-liner

