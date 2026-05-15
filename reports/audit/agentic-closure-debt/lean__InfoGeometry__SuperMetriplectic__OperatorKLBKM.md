# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:43.760833+00:00`
Root: `lean/InfoGeometry/SuperMetriplectic/OperatorKLBKM.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **33**
- Hard: **0**
- Soft: **32**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/SuperMetriplectic/OperatorKLBKM.lean` | `advisory` | 65 | 0 | 32 | 1 | 33 |

## Findings by file

### `lean/InfoGeometry/SuperMetriplectic/OperatorKLBKM.lean`
- module: `InfoGeometry.SuperMetriplectic.OperatorKLBKM`
- status: `advisory`
- debt_score: `65`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field UnnormalizedGaussianKLSplit.generalizedKL_eq_shape_add_scale` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field UnnormalizedGaussianKLSplit.shape_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field UnnormalizedGaussianKLSplit.scale_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field TypeIIIExpectationCarrier.vacuumExpectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field TypeIIIExpectationCarrier.perturbedExpectation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L69 [soft] `law-field-locker` in `structure-field TypeIIIExpectationCarrier.expectationRatio` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field TypeIIIExpectationCarrier.referenceVacuumWeight_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field TypeIIIExpectationCarrier.expectationRatio_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field OperatorLogBregmanLift.logGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L94 [soft] `law-field-locker` in `structure-field OperatorLogBregmanLift.modularHamiltonianReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L95 [soft] `law-field-locker` in `structure-field OperatorLogBregmanLift.operatorBregmanDivergence` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [soft] `law-field-locker` in `structure-field OperatorLogBregmanLift.generator_matches_modularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L98 [soft] `law-field-locker` in `structure-field OperatorLogBregmanLift.divergence_eq_generator_gap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field OperatorKLExponentialSecondOrderPacket.secondOrderTaylor_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L135 [soft] `law-field-locker` in `structure-field OperatorKLExponentialSecondOrderPacket.expKernel_eq_taylor_add_remainder` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.bkm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.hessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.modularIntegralReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.bkm_eq_modularIntegral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.hessian_eq_bkm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.bkm_symm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field OperatorBKMHessianPacket.bkm_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.bilinearOperatorProduct` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.scalarChannel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.vectorChannel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L214 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.spinTwoChannel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L215 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.linearizedGravityPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L216 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.fierz_decomposition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field FierzSpinTwoExtractionPacket.gravityPotential_eq_spinTwo` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L246 [soft] `law-field-locker` in `structure-field TypeIIIOperatorSupervolumePacket.superVolume_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L271 [soft] `law-field-locker` in `structure-field OperatorKLBKMCapstone.kernelDivergence_matches_gaussianKL` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L273 [soft] `law-field-locker` in `structure-field OperatorKLBKMCapstone.superVolume_bkm_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

