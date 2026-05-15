# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:13.374044+00:00`
Root: `lean/InfoGeometry/Canonical/WeylTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **15**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylTransport.lean` | `advisory` | 31 | 0 | 15 | 1 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylTransport.lean`
- module: `InfoGeometry.Canonical.WeylTransport`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [soft] `law-field-locker` in `structure-field WeylTrajectory.point` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field WeylLineIntegrator.integrate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L28 [soft] `law-field-locker` in `structure-field WeylHolonomyMap.toHolonomy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field ScaleEquivariantFlow.flowOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field ScaleEquivariantFlow.scaleOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `simp-law-injection` in `simp-declaration connectionAlong_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration generatedAlong_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration responseAlong_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration responseAlong_eq_along_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration curvatureAlong_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration covariantSectionAlong_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `simp-law-injection` in `simp-declaration covariantGeneratedFlow_flowOf_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [soft] `simp-law-injection` in `simp-declaration covariantGeneratedFlow_scaleOf_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L209 [soft] `simp-law-injection` in `simp-declaration respondCovariantFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L320 [soft] `skeletal-proof` in `theorem integrateCurvature_transformByPotential_eq` — proof appears to close via minimal tactic one-liner

