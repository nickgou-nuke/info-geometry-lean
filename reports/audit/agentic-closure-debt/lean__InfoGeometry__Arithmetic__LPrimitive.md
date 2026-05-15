# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:32.157546+00:00`
Root: `lean/InfoGeometry/Arithmetic/LPrimitive.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **7**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Arithmetic/LPrimitive.lean` | `advisory` | 18 | 0 | 7 | 4 | 11 |

## Findings by file

### `lean/InfoGeometry/Arithmetic/LPrimitive.lean`
- module: `InfoGeometry.Arithmetic.LPrimitive`
- status: `advisory`
- debt_score: `18`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [advisory] `existential-packaging` in `def LMultiple` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L45 [advisory] `existential-packaging` in `def LMultiplesOfSet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L84 [advisory] `existential-packaging` in `theorem mem_LMultiplesOfSet_iff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L84 [soft] `skeletal-proof` in `theorem mem_LMultiplesOfSet_iff` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `law-field-locker` in `structure-field LTrichotomyInput.trichotomy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L134 [soft] `law-field-locker` in `structure-field LMultipleDensityWitness.density_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field LPrimitiveLogDensityWitness.density_eq_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field LichtmanLocalBoundInput.localBoundLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field LichtmanLocalBoundInput.lDensityLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field LichtmanLocalBoundInput.mertensProductLaw` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

