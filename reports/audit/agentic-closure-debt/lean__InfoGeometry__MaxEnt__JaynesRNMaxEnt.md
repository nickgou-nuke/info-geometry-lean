# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:00.494303+00:00`
Root: `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/JaynesRNMaxEnt.lean`
- module: `InfoGeometry.MaxEnt.JaynesRNMaxEnt`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [soft] `law-field-locker` in `structure-field MomentFamily.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L19 [soft] `law-field-locker` in `structure-field MomentFamily.measurable_f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L20 [soft] `law-field-locker` in `structure-field MomentFamily.d` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L83 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L83 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L118 [soft] `skeletal-proof` in `theorem rnDeriv_gibbsMeasure_eq` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem partitionFunction_pos` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `skeletal-proof` in `theorem rnDeriv_gibbsMeasure_toReal_eq` — proof appears to close via minimal tactic one-liner
  - L157 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_gibbsMeasure_toReal_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

