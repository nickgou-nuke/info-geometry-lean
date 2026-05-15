# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:16.183696+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/IsROrK.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/IsROrK.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/IsROrK.lean`
- module: `InfoGeometry.OperatorAlgebra.IsROrK`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L16 [soft] `law-field-locker` in `class-field IsROrK.sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `class-field IsROrK.sigma_invol` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L18 [soft] `law-field-locker` in `class-field IsROrK.sigma_selfAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `simp-law-injection` in `simp-declaration sigma_invol_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L25 [advisory] `local-hypothesis-injection` in `class IsROrK` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

