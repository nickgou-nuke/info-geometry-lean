# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:44.155315+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **37**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean` | `advisory` | 77 | 0 | 37 | 3 | 40 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/SouriauTomitaBKM.lean`
- module: `InfoGeometry.SuperMetriplectic.SouriauTomitaBKM`
- status: `advisory`
- debt_score: `77`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field SouriauTomitaTemperatureDictionary.momentPairing_eq_beta_J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field SouriauTomitaTemperatureDictionary.modularHamiltonian_eq_momentPairing` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field SouriauTomitaTemperatureDictionary.modularDeltaLog_eq_modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field SouriauTomitaTemperatureDictionary.thermalTime_eq_modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field SouriauBKMHessianDictionary.souriauMassieuHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field SouriauBKMHessianDictionary.classicalCovarianceReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [soft] `law-field-locker` in `structure-field SouriauBKMHessianDictionary.souriauHessian_eq_classicalCovariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L82 [soft] `law-field-locker` in `structure-field SouriauBKMHessianDictionary.operatorLift_eq_bkm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field SouriauModularFoliationDictionary.coadjoint_eq_modularSpectrum` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L124 [soft] `law-field-locker` in `structure-field SouriauModularFoliationDictionary.alongLeafEntropyProduction_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field SouriauModularFoliationDictionary.transverseMotion_eq_arakiProduction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L154 [soft] `law-field-locker` in `structure-field SouriauTomitaBKMCapstone.bkm_matches_operatorKL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L156 [soft] `law-field-locker` in `structure-field SouriauTomitaBKMCapstone.supervolume_expectation_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field SouriauTomitaDerivationDictionary.souriauLieDerivation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field SouriauTomitaDerivationDictionary.tomitaModularDerivation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field SouriauTomitaDerivationDictionary.thermalTimeDerivation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field SouriauTomitaDerivationDictionary.souriau_eq_tomita` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L228 [soft] `law-field-locker` in `structure-field SouriauTomitaDerivationDictionary.thermalTime_eq_tomita` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L260 [soft] `law-field-locker` in `structure-field ThermalTimeHypothesisPacket.souriauThermalFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L261 [soft] `law-field-locker` in `structure-field ThermalTimeHypothesisPacket.tomitaModularFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L262 [soft] `law-field-locker` in `structure-field ThermalTimeHypothesisPacket.thermalTimeFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L263 [soft] `law-field-locker` in `structure-field ThermalTimeHypothesisPacket.souriauFlow_eq_tomita` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L265 [soft] `law-field-locker` in `structure-field ThermalTimeHypothesisPacket.thermalTimeFlow_eq_tomita` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L297 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.relativeEntropyGradientFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L298 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.souriauBKMGradientFlow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L299 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.linearizedGravityPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L300 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.spinTwoFierzChannel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L301 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.relativeEntropyGradient_eq_souriauBKM` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L303 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.souriauBKMGradient_eq_gravityPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L305 [soft] `law-field-locker` in `structure-field OperatorGradientGravityPacket.gravityPotential_eq_spinTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [advisory] `existential-packaging` in `theorem thermal_time_hypothesis_theorem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L389 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L438 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.analyticStripResolved` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L439 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.kmsBoundaryResidualControlled` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L440 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.matsubaraModeDiagonal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L441 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.sinkhornPerelmanSolverReady` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L442 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.chebyshev_resolves_solver` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L447 [soft] `law-field-locker` in `structure-field KMSImaginaryTimeDiscretizationPolicy.matsubara_is_diagnostic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L484 [soft] `law-field-locker` in `structure-field SinkhornPerelmanBKMQuadratureChoice.selected_chebyshev` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

