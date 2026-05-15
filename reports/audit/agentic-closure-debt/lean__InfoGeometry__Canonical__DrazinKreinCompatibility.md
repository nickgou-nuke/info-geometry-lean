# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.712072+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **12**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean` | `advisory` | 31 | 0 | 12 | 7 | 19 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinKreinCompatibility.lean`
- module: `InfoGeometry.Canonical.DrazinKreinCompatibility`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L79 [soft] `law-field-locker` in `structure-field IsCartanCompatible.eta_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field IsCartanCompatible.epsilon_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field IsCartanCompatible.modularJ_comm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field KreinGradedDrazinCompatibility.J_comm_T` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field KreinGradedDrazinCompatibility.J_comm_TD` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L109 [advisory] `bridge-shaped-declaration` in `def isCartanCompatible_T_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L119 [advisory] `bridge-shaped-declaration` in `def isCartanCompatible_TD_of_compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L198 [soft] `skeletal-proof` in `theorem Preg_mul_regularCompression` — proof appears to close via minimal tactic one-liner
  - L216 [soft] `skeletal-proof` in `theorem regularCompression_mul_Preg` — proof appears to close via minimal tactic one-liner
  - L234 [soft] `skeletal-proof` in `theorem Pzero_mul_regularCompression_eq_zero` — proof appears to close via minimal tactic one-liner
  - L251 [soft] `skeletal-proof` in `theorem regularCompression_mul_Pzero_eq_zero` — proof appears to close via minimal tactic one-liner
  - L299 [advisory] `local-hypothesis-injection` in `theorem commutes_with_Preg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [advisory] `local-hypothesis-injection` in `theorem commutes_with_Preg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L318 [advisory] `local-hypothesis-injection` in `theorem commutes_with_Pzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L484 [soft] `skeletal-proof` in `theorem complex_i_comm_Preg_of_drazinKreinCompatibility` — proof appears to close via minimal tactic one-liner
  - L498 [soft] `skeletal-proof` in `theorem complex_i_comm_Pzero_of_drazinKreinCompatibility` — proof appears to close via minimal tactic one-liner
  - L554 [soft] `law-field-locker` in `structure-field DefectSectorData.compat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

