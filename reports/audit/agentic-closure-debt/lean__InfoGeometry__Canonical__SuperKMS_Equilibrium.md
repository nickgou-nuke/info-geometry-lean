# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:02.980882+00:00`
Root: `lean/InfoGeometry/Canonical/SuperKMS_Equilibrium.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperKMS_Equilibrium.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperKMS_Equilibrium.lean`
- module: `InfoGeometry.Canonical.SuperKMS_Equilibrium`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field SuperchargeInteractionVertex.emit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field SuperchargeInteractionVertex.absorb` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field SuperKMSEquilibriumState.detailedBalance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `skeletal-proof` in `theorem constructive_detailed_balance` — proof appears to close via minimal tactic one-liner
  - L85 [soft] `skeletal-proof` in `theorem dirac_mass_term_is_equilibrium_constant` — proof appears to close via minimal tactic one-liner

