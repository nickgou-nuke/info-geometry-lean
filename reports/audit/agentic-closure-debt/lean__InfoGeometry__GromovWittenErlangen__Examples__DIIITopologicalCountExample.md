# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:42.968274+00:00`
Root: `lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **3**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean` | `advisory` | 7 | 0 | 3 | 1 | 4 |

## Findings by file

### `lean/InfoGeometry/GromovWittenErlangen/Examples/DIIITopologicalCountExample.lean`
- module: `InfoGeometry.GromovWittenErlangen.Examples.DIIITopologicalCountExample`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L60 [soft] `law-field-locker` in `structure-field DIIIZ2SectorWitness.topologicalIndexZ2_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `skeletal-proof` in `theorem counts_zero` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem counts_one` — proof appears to close via minimal tactic one-liner

