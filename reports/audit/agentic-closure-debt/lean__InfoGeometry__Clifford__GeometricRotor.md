# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:17.554811+00:00`
Root: `lean/InfoGeometry/Clifford/GeometricRotor.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **5**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/GeometricRotor.lean` | `advisory` | 17 | 0 | 5 | 7 | 12 |

## Findings by file

### `lean/InfoGeometry/Clifford/GeometricRotor.lean`
- module: `InfoGeometry.Clifford.GeometricRotor`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field Bivector.op` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field Bivector.square_neg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `skeletal-proof` in `theorem exp_reverse` — proof appears to close via minimal tactic one-liner
  - L48 [advisory] `local-hypothesis-injection` in `theorem exp_reverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L54 [advisory] `local-hypothesis-injection` in `theorem exp_reverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L65 [advisory] `local-hypothesis-injection` in `theorem exp_reverse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [soft] `skeletal-proof` in `theorem reverse_comp_exp` — proof appears to close via minimal tactic one-liner
  - L75 [advisory] `local-hypothesis-injection` in `theorem reverse_comp_exp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [advisory] `local-hypothesis-injection` in `theorem reverse_comp_exp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [advisory] `local-hypothesis-injection` in `theorem reverse_comp_exp` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L105 [soft] `simp-law-injection` in `simp-declaration evolve_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

