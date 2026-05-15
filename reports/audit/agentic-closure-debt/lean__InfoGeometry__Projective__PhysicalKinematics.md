# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:31.482546+00:00`
Root: `lean/InfoGeometry/Projective/PhysicalKinematics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/PhysicalKinematics.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Projective/PhysicalKinematics.lean`
- module: `InfoGeometry.Projective.PhysicalKinematics`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L21 [soft] `law-field-locker` in `structure-field PhysicalKinematics.ray` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field PhysicalKinematics.ray_gauge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `bridge-shaped-declaration` in `lemma GaugeInvariant.compat` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L61 [soft] `simp-law-injection` in `simp-declaration descend_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `simp-law-injection` in `simp-declaration liftGaugeInvariant_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration occupancyOnProjective_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration occupancy_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `skeletal-proof` in `lemma occupancy_eq_one_iff` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `simp-law-injection` in `simp-declaration occupancyOnProjective_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `skeletal-proof` in `lemma occupancyOnProjective_of_ne_zero` — proof appears to close via minimal tactic one-liner

