# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:29.364544+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Class.lean`
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
| `lean/InfoGeometry/ExponentialFamily/Class.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Class.lean`
- module: `InfoGeometry.ExponentialFamily.Class`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L11 [soft] `law-field-locker` in `class-field ExponentialFamily.statistic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L12 [soft] `law-field-locker` in `class-field ExponentialFamily.logPartition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L13 [soft] `law-field-locker` in `class-field ExponentialFamily.density` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L14 [soft] `law-field-locker` in `class-field ExponentialFamily.density_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `class-field FiniteExponentialFamily.normalization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [advisory] `existential-packaging` in `lemma density_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [advisory] `local-hypothesis-injection` in `lemma multinomial_density_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

