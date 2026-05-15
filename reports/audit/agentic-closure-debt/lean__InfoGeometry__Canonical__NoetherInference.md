# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:33.263590+00:00`
Root: `lean/InfoGeometry/Canonical/NoetherInference.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/NoetherInference.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/NoetherInference.lean`
- module: `InfoGeometry.Canonical.NoetherInference`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `skeletal-proof` in `theorem InformationKillingField.preserves_hessian` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration evalAt_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration fisherBilinAt_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L97 [advisory] `local-hypothesis-injection` in `theorem fisherBilinAt_conjugate_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `local-hypothesis-injection` in `theorem fisherBilinAt_conjugate_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [soft] `skeletal-proof` in `theorem killing_form_conjugate_eq` — proof appears to close via minimal tactic one-liner
  - L228 [advisory] `local-hypothesis-injection` in `theorem theta_commutes_with_operator_conjugation_of_commutes_with_involution` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L363 [soft] `law-field-locker` in `structure-field BayesianSymmetryOrbit.generator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L364 [soft] `law-field-locker` in `structure-field BayesianSymmetryOrbit.U` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L365 [soft] `law-field-locker` in `structure-field BayesianSymmetryOrbit.U_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L366 [soft] `law-field-locker` in `structure-field BayesianSymmetryOrbit.preserves_hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L377 [soft] `simp-law-injection` in `simp-declaration BayesianSymmetryOrbit.update_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L383 [soft] `simp-law-injection` in `simp-declaration BayesianSymmetryOrbit.update_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

