# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:39.870814+00:00`
Root: `lean/InfoGeometry/Geometry/SpectralDivisors.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **23**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/SpectralDivisors.lean` | `advisory` | 56 | 0 | 23 | 10 | 33 |

## Findings by file

### `lean/InfoGeometry/Geometry/SpectralDivisors.lean`
- module: `InfoGeometry.Geometry.SpectralDivisors`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L152 [soft] `law-field-locker` in `structure-field KernelAdmissibilityComplete.admissible_of_isUnit_diff` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [soft] `law-field-locker` in `structure-field SpectralDivisorDatum.F` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L215 [soft] `law-field-locker` in `structure-field SpectralDivisorDatum.multiplicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L217 [soft] `law-field-locker` in `structure-field SpectralDivisorDatum.multiplicity_zero_off_divisor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L259 [soft] `law-field-locker` in `structure-field LogDerivativeDatum.invF` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L261 [soft] `law-field-locker` in `structure-field LogDerivativeDatum.analytic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field LogDerivativeDatum.left_inverse_branch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field LogDerivativeDatum.right_inverse_branch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L281 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L367 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L420 [soft] `skeletal-proof` in `theorem phasePeriod_eq` — proof appears to close via minimal tactic one-liner
  - L449 [soft] `law-field-locker` in `structure-field WindingNumberDatum.winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L451 [soft] `law-field-locker` in `structure-field WindingNumberDatum.residue_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L465 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L579 [soft] `law-field-locker` in `structure-field FiniteDivisorCounter.enclosedDivisors` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L593 [soft] `skeletal-proof` in `theorem enclosedMultiplicity_eq_sum` — proof appears to close via minimal tactic one-liner
  - L624 [soft] `law-field-locker` in `structure-field DivisorWindingCalibration.winding_eq_enclosedMultiplicity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L641 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L648 [soft] `skeletal-proof` in `theorem enclosedMultiplicity_eq_sum` — proof appears to close via minimal tactic one-liner
  - L684 [advisory] `local-hypothesis-injection` in `theorem boundaryIntegral_eq_zero_iff_enclosedMultiplicity_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L725 [soft] `law-field-locker` in `structure-field TopologicalIndexDatum.regionOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L727 [soft] `law-field-locker` in `structure-field TopologicalIndexDatum.index` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L729 [soft] `law-field-locker` in `structure-field TopologicalIndexDatum.spectralFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L731 [soft] `law-field-locker` in `structure-field TopologicalIndexDatum.index_eq_winding` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L735 [soft] `law-field-locker` in `structure-field TopologicalIndexDatum.index_eq_spectralFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L749 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L842 [soft] `law-field-locker` in `structure-field SpectralFunctionCalibration.spectralFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L844 [soft] `law-field-locker` in `structure-field SpectralFunctionCalibration.divisorDatum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L846 [soft] `law-field-locker` in `structure-field SpectralFunctionCalibration.divisorDatum_F` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L855 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

