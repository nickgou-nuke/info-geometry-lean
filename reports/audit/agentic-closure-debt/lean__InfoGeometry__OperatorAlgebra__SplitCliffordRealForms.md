# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:22.982863+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/SplitCliffordRealForms.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **5**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/SplitCliffordRealForms.lean` | `advisory` | 14 | 0 | 5 | 4 | 9 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/SplitCliffordRealForms.lean`
- module: `InfoGeometry.OperatorAlgebra.SplitCliffordRealForms`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L167 [advisory] `local-hypothesis-injection` in `theorem mem_fixed_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L188 [advisory] `local-hypothesis-injection` in `theorem mem_antiFixed_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L300 [soft] `law-field-locker` in `structure-field GWRealFormCriterion.complement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L303 [soft] `law-field-locker` in `structure-field GWRealFormCriterion.complement_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L307 [soft] `law-field-locker` in `structure-field GWRealFormCriterion.measure_equivalent_under_complement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L315 [soft] `law-field-locker` in `structure-field GWRealFormCriterion.multiplicity_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L323 [soft] `law-field-locker` in `structure-field GWRealFormCriterion.measurable_real_cocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

