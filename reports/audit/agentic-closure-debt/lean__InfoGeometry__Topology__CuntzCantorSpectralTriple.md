# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:49.485750+00:00`
Root: `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **24**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean` | `advisory` | 53 | 0 | 24 | 5 | 29 |

## Findings by file

### `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean`
- module: `InfoGeometry.Topology.CuntzCantorSpectralTriple`
- status: `advisory`
- debt_score: `53`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `skeletal-proof` in `theorem prefixBoundary_zero` — proof appears to close via minimal tactic one-liner
  - L52 [soft] `skeletal-proof` in `theorem prefixBoundary_succ` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `law-field-locker` in `structure-field CuntzO2Carrier.left_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field CuntzO2Carrier.right_isometry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field CuntzO2Carrier.orthogonal_ranges` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field CuntzO2Carrier.range_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L99 [soft] `skeletal-proof` in `theorem leftRangeProjection_idempotent` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem rightRangeProjection_idempotent` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem leftRange_mul_rightRange_eq_zero` — proof appears to close via minimal tactic one-liner
  - L141 [soft] `skeletal-proof` in `theorem rightRange_mul_leftRange_eq_zero` — proof appears to close via minimal tactic one-liner
  - L161 [soft] `law-field-locker` in `structure-field CuntzMajoranaCandidates.phaseI_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L179 [soft] `skeletal-proof` in `theorem e1_eq` — proof appears to close via minimal tactic one-liner
  - L184 [soft] `skeletal-proof` in `theorem e2_eq` — proof appears to close via minimal tactic one-liner
  - L206 [soft] `law-field-locker` in `structure-field MajoranaCARWitness.e1_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field MajoranaCARWitness.e2_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field MajoranaCARWitness.anticommute` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.cylinderRepresentation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.dirac` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.representedAction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L230 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.boundedCommutatorWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.compactResolventOrSummability` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field CuntzCantorSpectralTriple.cantorDimensionCalibration` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L298 [soft] `law-field-locker` in `structure-field ErlangenNetCuntzRealization.leftPrefixRealization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L302 [soft] `law-field-locker` in `structure-field ErlangenNetCuntzRealization.rightPrefixRealization` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L311 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

