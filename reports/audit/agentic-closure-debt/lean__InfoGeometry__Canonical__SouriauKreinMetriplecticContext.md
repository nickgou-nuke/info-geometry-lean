# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:57.226599+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **41**
- Hard: **0**
- Soft: **25**
- Advisory: **16**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean` | `advisory` | 66 | 0 | 25 | 16 | 41 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauKreinMetriplecticContext.lean`
- module: `InfoGeometry.Canonical.SouriauKreinMetriplecticContext`
- status: `advisory`
- debt_score: `66`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L54 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L67 [soft] `law-field-locker` in `structure-field OperatorialMetriplecticContext.P` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L79 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `section-law-variable` in `variable C` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L197 [soft] `skeletal-proof` in `theorem metricResponse_swap` — proof appears to close via minimal tactic one-liner
  - L204 [soft] `skeletal-proof` in `theorem mixedMetricResponse_symm` — proof appears to close via minimal tactic one-liner
  - L248 [soft] `law-field-locker` in `structure-field SquareOperatorialResponseContext.diagonalMetricResponse_eq_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L250 [soft] `law-field-locker` in `structure-field SquareOperatorialResponseContext.yDiagonalMetricResponse_eq_square` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L252 [soft] `law-field-locker` in `structure-field SquareOperatorialResponseContext.mixedMetricResponseXY_eq_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L283 [advisory] `local-hypothesis-injection` in `theorem operatorialMetricResponsePSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L305 [soft] `law-field-locker` in `structure-field RegularConeXResponseContext.c` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L308 [soft] `law-field-locker` in `structure-field RegularConeXResponseContext.probe_nonneg_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `law-field-locker` in `structure-field RegularConeXResponseContext.diagonalMetricResponse_eq_probe_Hxx` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L339 [soft] `law-field-locker` in `structure-field RegularConeOperatorialResponseContext.c` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L344 [soft] `law-field-locker` in `structure-field RegularConeOperatorialResponseContext.probe_nonneg_on_regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L346 [soft] `law-field-locker` in `structure-field RegularConeOperatorialResponseContext.diagonalMetricResponse_eq_probe_Hxx` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L348 [soft] `law-field-locker` in `structure-field RegularConeOperatorialResponseContext.yDiagonalMetricResponse_eq_probe_Hyy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L350 [soft] `law-field-locker` in `structure-field RegularConeOperatorialResponseContext.mixed_determinant_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L400 [soft] `law-field-locker` in `structure-field CramerRaoOperatorialResponseContext.diagonalMetricResponse_eq_comparisonMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L403 [soft] `law-field-locker` in `structure-field CramerRaoOperatorialResponseContext.yDiagonalMetricResponse_eq_comparisonMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L406 [soft] `law-field-locker` in `structure-field CramerRaoOperatorialResponseContext.mixedMetricResponseXY_eq_comparisonMetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L441 [advisory] `local-hypothesis-injection` in `theorem mixed_determinant_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L473 [advisory] `local-hypothesis-injection` in `theorem operatorialEntropyProduction_nonneg_of_metricResponsePSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L480 [advisory] `local-hypothesis-injection` in `theorem operatorialEntropyProduction_nonneg_of_metricResponsePSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L482 [advisory] `local-hypothesis-injection` in `theorem operatorialEntropyProduction_nonneg_of_metricResponsePSD` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L566 [advisory] `local-hypothesis-injection` in `theorem canonicalEntropyProduction_nonneg_of_cramerRaoResponse` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L584 [advisory] `local-hypothesis-injection` in `theorem canonicalEntropyProduction_nonneg_of_regularCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L600 [advisory] `bridge-shaped-declaration` in `theorem supergradedEvenOddOnsagerBlock_packet_of_cramerRaoResponse` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L638 [advisory] `local-hypothesis-injection` in `theorem operatorialEntropyProduction_xChannel_nonneg_of_regularCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L640 [advisory] `local-hypothesis-injection` in `theorem operatorialEntropyProduction_xChannel_nonneg_of_regularCone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L645 [soft] `skeletal-proof` in `theorem metricResponse_eq_half_probe_observableLieHessian_add_swap` — proof appears to close via minimal tactic one-liner
  - L656 [soft] `skeletal-proof` in `theorem diagonalMetricResponse_eq_probe_double_transportCommutator` — proof appears to close via minimal tactic one-liner
  - L667 [soft] `skeletal-proof` in `theorem curvatureResponse_swap_neg` — proof appears to close via minimal tactic one-liner
  - L674 [soft] `skeletal-proof` in `theorem curvatureResponse_eq_probe_bracketDerivation` — proof appears to close via minimal tactic one-liner
  - L686 [soft] `skeletal-proof` in `theorem jReflectedPhaseCorrelation_eq_neg` — proof appears to close via minimal tactic one-liner
  - L697 [soft] `skeletal-proof` in `theorem weightedDynamics_eq_zeroWeight_add_phaseAxisCommutator` — proof appears to close via minimal tactic one-liner
  - L709 [soft] `skeletal-proof` in `theorem weightedDynamics_eq_weylCovariantThermodynamicDerivation` — proof appears to close via minimal tactic one-liner
  - L744 [advisory] `bridge-shaped-declaration` in `theorem operatorialDilationGoldstoneCharge_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L786 [advisory] `bridge-shaped-declaration` in `theorem supergradedFisherOnsagerBlock_squareResponse_CAR_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

