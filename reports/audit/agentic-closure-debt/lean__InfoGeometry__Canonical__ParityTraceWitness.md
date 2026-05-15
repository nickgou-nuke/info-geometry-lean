# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:40.305175+00:00`
Root: `lean/InfoGeometry/Canonical/ParityTraceWitness.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **7**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ParityTraceWitness.lean` | `advisory` | 16 | 0 | 7 | 2 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/ParityTraceWitness.lean`
- module: `InfoGeometry.Canonical.ParityTraceWitness`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field BooleanPrimeStateArithmetic.representedBySubset` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field BooleanPrimeStateArithmetic.subset_represents` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [advisory] `local-hypothesis-injection` in `theorem mobius_squarefree_subset_eq_weyl_sign` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [soft] `skeletal-proof` in `theorem nonsquarefree_not_represented_by_boolean_prime_state` — proof appears to close via minimal tactic one-liner
  - L106 [soft] `skeletal-proof` in `theorem parityCoeff_eq_mobius` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem fermionCoeff_eq_abs_mobius` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `theorem fermionCoeff_eq_absMobius` — proof appears to close via minimal tactic one-liner
  - L128 [soft] `skeletal-proof` in `theorem splitParityCoefficient_eq_mobius` — proof appears to close via minimal tactic one-liner

