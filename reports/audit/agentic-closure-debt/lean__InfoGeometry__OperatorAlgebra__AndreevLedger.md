# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:05.482857+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/AndreevLedger.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/AndreevLedger.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/AndreevLedger.lean`
- module: `InfoGeometry.OperatorAlgebra.AndreevLedger`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `law-field-locker` in `structure-field AndreevLedger.delta_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L58 [soft] `skeletal-proof` in `theorem zero_subgap` — proof appears to close via minimal tactic one-liner
  - L82 [soft] `law-field-locker` in `structure-field AndreevPair.electron_to_hole` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L155 [soft] `law-field-locker` in `structure-field BdGHamiltonianLedger.H` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field BdGHamiltonianLedger.particle_hole_anticommutes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L178 [soft] `skeletal-proof` in `theorem particle_hole_flips_energy` — proof appears to close via minimal tactic one-liner
  - L196 [soft] `skeletal-proof` in `theorem particle_hole_preserves_zeroMode` — proof appears to close via minimal tactic one-liner
  - L276 [soft] `law-field-locker` in `structure-field VortexCoreMajoranaWitness.localized_at_core` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L290 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

