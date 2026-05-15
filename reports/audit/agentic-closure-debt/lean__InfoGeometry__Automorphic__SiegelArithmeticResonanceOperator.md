# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:36.077641+00:00`
Root: `lean/InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **43**
- Hard: **0**
- Soft: **28**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean` | `advisory` | 71 | 0 | 28 | 15 | 43 |

## Findings by file

### `lean/InfoGeometry/Automorphic/SiegelArithmeticResonanceOperator.lean`
- module: `InfoGeometry.Automorphic.SiegelArithmeticResonanceOperator`
- status: `advisory`
- debt_score: `71`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L68 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L153 [soft] `law-field-locker` in `structure-field SiegelArithmeticReadoutCalibration.rawReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field SiegelArithmeticReadoutCalibration.resonanceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [soft] `law-field-locker` in `structure-field SiegelArithmeticReadoutCalibration.resonanceReadout_eq_raw_pure` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L205 [soft] `law-field-locker` in `structure-field SiegelZetaTraceCalibration.arithmeticAmplitude` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L259 [soft] `law-field-locker` in `structure-field JordanSiegelNormReduction.cubicNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L261 [soft] `law-field-locker` in `structure-field JordanSiegelNormReduction.boundaryNorm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L264 [soft] `law-field-locker` in `structure-field JordanSiegelNormReduction.boundaryLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L267 [soft] `law-field-locker` in `structure-field JordanSiegelNormReduction.cubicNorm_boundaryLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L276 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L283 [soft] `skeletal-proof` in `theorem cubicNorm_boundaryLift_eq` — proof appears to close via minimal tactic one-liner
  - L322 [soft] `law-field-locker` in `structure-field JordanSiegelPotentialReduction.cubicPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L324 [soft] `law-field-locker` in `structure-field JordanSiegelPotentialReduction.boundaryPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L327 [soft] `law-field-locker` in `structure-field JordanSiegelPotentialReduction.boundaryLift` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L330 [soft] `law-field-locker` in `structure-field JordanSiegelPotentialReduction.renormalizedPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L333 [soft] `law-field-locker` in `structure-field JordanSiegelPotentialReduction.renormalizedPotential_eq_boundary` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L342 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L370 [soft] `law-field-locker` in `structure-field ExceptionalSiegelConstantTermLayer.constantTerm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L372 [soft] `law-field-locker` in `structure-field ExceptionalSiegelConstantTermLayer.constantTerm_eq_siegel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L383 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L417 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.eulerLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L418 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.logZeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L419 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.surprisal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L420 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.freeEnergy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L421 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.logZeta_eq_neg_eulerLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L424 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.surprisal_eq_logZeta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L427 [soft] `law-field-locker` in `structure-field ZetaSurprisalSignConvention.freeEnergy_eq_eulerLog` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L434 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L459 [soft] `law-field-locker` in `structure-field FiniteMobiusPrimeFilter.coefficient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L462 [soft] `law-field-locker` in `structure-field FiniteMobiusPrimeFilter.logZetaMode` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L465 [soft] `law-field-locker` in `structure-field FiniteMobiusPrimeFilter.primeResonance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L468 [soft] `law-field-locker` in `structure-field FiniteMobiusPrimeFilter.primeResonance_eq_mobius_sum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L478 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L514 [soft] `law-field-locker` in `structure-field ThreeLayerSiegelResonanceOperator.boundaryToBulk` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L535 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L564 [advisory] `existential-packaging` in `def SiegelArithmeticResonanceFilterOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L573 [advisory] `existential-packaging` in `def SiegelArithmeticReadoutOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L582 [advisory] `existential-packaging` in `def SiegelZetaTraceCalibrationOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L591 [advisory] `existential-packaging` in `def JordanSiegelNormReductionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L596 [advisory] `existential-packaging` in `def ThreeLayerSiegelResonanceOperatorOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

