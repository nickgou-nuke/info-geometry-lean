# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:17.923579+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/MobiusClosure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **5**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/MobiusClosure.lean` | `advisory` | 19 | 0 | 5 | 9 | 14 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/MobiusClosure.lean`
- module: `InfoGeometry.OperatorAlgebra.MobiusClosure`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.inv` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.inv_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field MobiusInversionDatum.preserves_null` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L63 [advisory] `existential-packaging` in `def IsProjectiveFixed` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L130 [advisory] `local-hypothesis-injection` in `theorem inv_projectiveFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L134 [soft] `skeletal-proof` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — proof appears to close via minimal tactic one-liner
  - L148 [advisory] `local-hypothesis-injection` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [advisory] `local-hypothesis-injection` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [advisory] `local-hypothesis-injection` in `theorem scale_sq_eq_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L173 [advisory] `local-hypothesis-injection` in `theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L176 [advisory] `local-hypothesis-injection` in `theorem scale_eq_one_or_neg_one_of_projectiveFixed_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [soft] `skeletal-proof` in `theorem symmetrizedReadout_inv` — proof appears to close via minimal tactic one-liner

