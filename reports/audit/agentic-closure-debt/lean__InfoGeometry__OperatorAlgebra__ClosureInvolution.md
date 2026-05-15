# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:07.714113+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **26**
- Hard: **0**
- Soft: **10**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean` | `advisory` | 36 | 0 | 10 | 16 | 26 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ClosureInvolution.lean`
- module: `InfoGeometry.OperatorAlgebra.ClosureInvolution`
- status: `advisory`
- debt_score: `36`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field LinearClosureInvolution.theta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field LinearClosureInvolution.theta_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L253 [advisory] `local-hypothesis-injection` in `theorem fixedPart_eq_self_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L264 [advisory] `local-hypothesis-injection` in `theorem antiPart_eq_zero_of_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L275 [advisory] `local-hypothesis-injection` in `theorem fixedPart_eq_zero_of_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L286 [advisory] `local-hypothesis-injection` in `theorem antiPart_eq_self_of_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L423 [soft] `simp-law-injection` in `simp-declaration fixedProjection_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L425 [soft] `skeletal-proof` in `theorem fixedProjection_apply` — proof appears to close via minimal tactic one-liner
  - L429 [soft] `simp-law-injection` in `simp-declaration antiProjection_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L431 [soft] `skeletal-proof` in `theorem antiProjection_apply` — proof appears to close via minimal tactic one-liner
  - L495 [soft] `skeletal-proof` in `theorem fixedProjection_theta` — proof appears to close via minimal tactic one-liner
  - L501 [soft] `skeletal-proof` in `theorem antiProjection_theta` — proof appears to close via minimal tactic one-liner
  - L531 [soft] `skeletal-proof` in `theorem ker_fixedProjection_eq_antiFixed` — proof appears to close via minimal tactic one-liner
  - L537 [advisory] `local-hypothesis-injection` in `theorem ker_fixedProjection_eq_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L539 [advisory] `local-hypothesis-injection` in `theorem ker_fixedProjection_eq_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L542 [advisory] `local-hypothesis-injection` in `theorem ker_fixedProjection_eq_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L545 [advisory] `local-hypothesis-injection` in `theorem ker_fixedProjection_eq_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L549 [advisory] `local-hypothesis-injection` in `theorem ker_fixedProjection_eq_antiFixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L557 [soft] `skeletal-proof` in `theorem ker_antiProjection_eq_fixed` — proof appears to close via minimal tactic one-liner
  - L563 [advisory] `local-hypothesis-injection` in `theorem ker_antiProjection_eq_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L565 [advisory] `local-hypothesis-injection` in `theorem ker_antiProjection_eq_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L568 [advisory] `local-hypothesis-injection` in `theorem ker_antiProjection_eq_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L571 [advisory] `local-hypothesis-injection` in `theorem ker_antiProjection_eq_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L575 [advisory] `local-hypothesis-injection` in `theorem ker_antiProjection_eq_fixed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

