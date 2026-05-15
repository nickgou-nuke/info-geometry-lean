# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:36.636623+00:00`
Root: `lean/InfoGeometry/Automorphic/SiegelWeilKudlaRallisBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **21**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/SiegelWeilKudlaRallisBridge.lean` | `advisory` | 50 | 0 | 21 | 8 | 29 |

## Findings by file

### `lean/InfoGeometry/Automorphic/SiegelWeilKudlaRallisBridge.lean`
- module: `InfoGeometry.Automorphic.SiegelWeilKudlaRallisBridge`
- status: `advisory`
- debt_score: `50`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `existential-packaging` in `def IsRationalComplex` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L62 [soft] `law-field-locker` in `structure-field RankinSelbergThetaIntegralWitness.rankinSelbergPairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field RankinSelbergThetaIntegralWitness.innerProductH` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field RankinSelbergThetaIntegralWitness.standardL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field RankinSelbergThetaIntegralWitness.badFactor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field RankinSelbergThetaIntegralWitness.rankinSelberg_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L153 [soft] `law-field-locker` in `structure-field SiegelWeilKudlaRallisFormulaWitness.eisenstein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field SiegelWeilKudlaRallisFormulaWitness.thetaTrivial` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L161 [soft] `law-field-locker` in `structure-field SiegelWeilKudlaRallisFormulaWitness.siegel_weil_formula` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L196 [soft] `law-field-locker` in `structure-field PullbackDecompositionFormulaWitness.pullbackEisenstein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L200 [soft] `law-field-locker` in `structure-field PullbackDecompositionFormulaWitness.evalLeft` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field PullbackDecompositionFormulaWitness.evalRight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L208 [soft] `law-field-locker` in `structure-field PullbackDecompositionFormulaWitness.normalizedCoefficient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field PullbackDecompositionFormulaWitness.decomposition_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L251 [soft] `law-field-locker` in `structure-field RationalFiniteFourierWitness.finiteFourierPart` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L254 [soft] `law-field-locker` in `structure-field RationalFiniteFourierWitness.finiteFourierPart_rational` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L282 [soft] `law-field-locker` in `structure-field NormalizedSpecialValueRationalityWitness.lambda` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L285 [soft] `law-field-locker` in `structure-field NormalizedSpecialValueRationalityWitness.selfInner` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L289 [soft] `law-field-locker` in `structure-field NormalizedSpecialValueRationalityWitness.normalizedSpecialValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `law-field-locker` in `structure-field NormalizedSpecialValueRationalityWitness.normalizedSpecialValue_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field NormalizedSpecialValueRationalityWitness.normalizedSpecialValue_rational` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L348 [soft] `law-field-locker` in `structure-field RankinSelbergProjectedLBridge.projected_eq_standard` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L365 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

