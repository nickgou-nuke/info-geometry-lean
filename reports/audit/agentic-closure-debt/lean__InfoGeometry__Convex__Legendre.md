# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.566117+00:00`
Root: `lean/InfoGeometry/Convex/Legendre.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **30**
- Hard: **0**
- Soft: **10**
- Advisory: **20**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/Legendre.lean` | `advisory` | 40 | 0 | 10 | 20 | 30 |

## Findings by file

### `lean/InfoGeometry/Convex/Legendre.lean`
- module: `InfoGeometry.Convex.Legendre`
- status: `advisory`
- debt_score: `40`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `law-field-locker` in `structure-field ConvexFunctional.F` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [advisory] `existential-packaging` in `def affineSet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L59 [advisory] `existential-packaging` in `lemma affineSet_nonempty` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L74 [advisory] `local-hypothesis-injection` in `theorem fenchel_young` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L77 [soft] `skeletal-proof` in `theorem supporting_ineq_of_convex_differentiable` — proof appears to close via minimal tactic one-liner
  - L93 [advisory] `local-hypothesis-injection` in `theorem supporting_ineq_of_convex_differentiable` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem supporting_ineq_of_convex_differentiable` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [advisory] `local-hypothesis-injection` in `theorem supporting_ineq_of_convex_differentiable` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L105 [advisory] `local-hypothesis-injection` in `theorem supporting_ineq_of_convex_differentiable` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `local-hypothesis-injection` in `theorem supporting_ineq_of_convex_differentiable` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L113 [soft] `skeletal-proof` in `theorem fenchel_young_eq_of_supporting` — proof appears to close via minimal tactic one-liner
  - L122 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L134 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [advisory] `local-hypothesis-injection` in `theorem fenchel_young_eq_of_supporting` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [soft] `skeletal-proof` in `theorem grad_injective_of_strictMonotone` — proof appears to close via minimal tactic one-liner
  - L165 [advisory] `local-hypothesis-injection` in `theorem grad_injective_of_strictMonotone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem grad_injective_of_strictMonotone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [soft] `law-field-locker` in `structure-field LegendrePotential.f` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [soft] `simp-law-injection` in `simp-declaration thetaOfEta_eta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L248 [soft] `skeletal-proof` in `theorem thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` — proof appears to close via minimal tactic one-liner
  - L270 [advisory] `local-hypothesis-injection` in `theorem thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L275 [advisory] `local-hypothesis-injection` in `theorem thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `local-hypothesis-injection` in `theorem thetaOfEta_deriv_eq_inv_fisher_of_hasDerivAt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L293 [soft] `simp-law-injection` in `simp-declaration bregman_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L305 [soft] `simp-law-injection` in `simp-declaration legendreTransform_eta` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L332 [soft] `skeletal-proof` in `theorem fenchel_young_eq_of_grad` — proof appears to close via minimal tactic one-liner

