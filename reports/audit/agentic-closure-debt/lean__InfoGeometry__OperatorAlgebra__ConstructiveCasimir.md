# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.567051+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConstructiveCasimir.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConstructiveCasimir.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConstructiveCasimir.lean`
- module: `InfoGeometry.OperatorAlgebra.ConstructiveCasimir`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `simp-law-injection` in `simp-declaration assocCommutator_zero_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L67 [soft] `skeletal-proof` in `theorem assocCommutator_zero_right` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `law-field-locker` in `structure-field VerifiedQuadraticCasimir.X` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L174 [soft] `law-field-locker` in `structure-field VerifiedQuadraticCasimir.Y` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `law-field-locker` in `structure-field VerifiedQuadraticCasimir.cancellation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L303 [advisory] `existential-packaging` in `def ConstructiveCasimirOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

