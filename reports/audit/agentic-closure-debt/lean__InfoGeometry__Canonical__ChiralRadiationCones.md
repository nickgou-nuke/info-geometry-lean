# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:52.776057+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralRadiationCones.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **7**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralRadiationCones.lean` | `advisory` | 15 | 0 | 7 | 1 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralRadiationCones.lean`
- module: `InfoGeometry.Canonical.ChiralRadiationCones`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [soft] `law-field-locker` in `structure-field ChiralRadiationCones.leftCone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L16 [soft] `law-field-locker` in `structure-field ChiralRadiationCones.rightCone` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `structure-field ChiralRadiationCones.toRight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L18 [soft] `law-field-locker` in `structure-field ChiralRadiationCones.toLeft` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field ChiralScatteringMass.mass_eq_flipRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `skeletal-proof` in `theorem constructive_mass_eq_flipRate` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `skeletal-proof` in `theorem diracMassTerm_eq_of_mass_eq_flipRate` — proof appears to close via minimal tactic one-liner

