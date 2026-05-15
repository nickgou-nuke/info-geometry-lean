# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:55.011339+00:00`
Root: `lean/InfoGeometry/Krein/Superphysics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/Superphysics.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Krein/Superphysics.lean`
- module: `InfoGeometry.Krein.Superphysics`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `law-field-locker` in `structure-field Supercharge.Q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `skeletal-proof` in `lemma superHamiltonian_isEven` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `lemma supercharge_maps_plus_to_minus` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `skeletal-proof` in `lemma supercharge_maps_minus_to_plus` — proof appears to close via minimal tactic one-liner

