# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.427148+00:00`
Root: `lean/InfoGeometry/Convex/HessianGeometry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **34**
- Hard: **0**
- Soft: **18**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/HessianGeometry.lean` | `advisory` | 52 | 0 | 18 | 16 | 34 |

## Findings by file

### `lean/InfoGeometry/Convex/HessianGeometry.lean`
- module: `InfoGeometry.Convex.HessianGeometry`
- status: `advisory`
- debt_score: `52`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `law-field-locker` in `class-field BregmanDivergence.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field HessianGeometry1D.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L40 [soft] `simp-law-injection` in `simp-declaration metric_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration dualMap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [advisory] `existential-packaging` in `def dualPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L58 [soft] `simp-law-injection` in `simp-declaration divergence_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [soft] `simp-law-injection` in `simp-declaration bregmanDiv_D` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [advisory] `existential-packaging` in `def softmaxBregmanAttention` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `law-field-locker` in `structure-field HessianGeometry.potential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field HessianGeometry.grad` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L97 [soft] `law-field-locker` in `structure-field HessianGeometry.has_gradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field HessianGeometry.divergence_nonneg_axiom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L108 [soft] `simp-law-injection` in `simp-declaration dualMap_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [soft] `simp-law-injection` in `simp-declaration metric_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `skeletal-proof` in `theorem divergence_nonneg` — proof appears to close via minimal tactic one-liner
  - L137 [soft] `skeletal-proof` in `theorem grad_monotone` — proof appears to close via minimal tactic one-liner
  - L143 [advisory] `local-hypothesis-injection` in `theorem grad_monotone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [advisory] `local-hypothesis-injection` in `theorem grad_monotone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L145 [advisory] `local-hypothesis-injection` in `theorem grad_monotone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L153 [soft] `skeletal-proof` in `theorem metricOp_isSymmetric` — proof appears to close via minimal tactic one-liner
  - L174 [soft] `skeletal-proof` in `theorem metric_quadratic_nonneg` — proof appears to close via minimal tactic one-liner
  - L187 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L191 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L193 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L215 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L217 [advisory] `local-hypothesis-injection` in `theorem metric_quadratic_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L223 [soft] `skeletal-proof` in `theorem metric_nonneg` — proof appears to close via minimal tactic one-liner
  - L239 [advisory] `existential-packaging` in `def dualPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L247 [soft] `simp-law-injection` in `simp-declaration bregmanDiv_D` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L250 [advisory] `existential-packaging` in `def softmaxBregmanAttention` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

