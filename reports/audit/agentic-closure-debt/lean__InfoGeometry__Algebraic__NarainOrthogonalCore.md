# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:28.635536+00:00`
Root: `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Algebraic/NarainOrthogonalCore.lean`
- module: `InfoGeometry.Algebraic.NarainOrthogonalCore`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field NarainChargeSymmetry.preserves_hyperbolicPair` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `simp-law-injection` in `simp-declaration apply_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `skeletal-proof` in `theorem apply_eq` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `simp-law-injection` in `simp-declaration chargeSwapLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem chargeSwapLinearEquiv_apply` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `skeletal-proof` in `theorem chargeSwap_preserves_hyperbolicPair` — proof appears to close via minimal tactic one-liner
  - L100 [soft] `simp-law-injection` in `simp-declaration chargeParityTwistLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `skeletal-proof` in `theorem chargeParityTwistLinearEquiv_apply` — proof appears to close via minimal tactic one-liner

