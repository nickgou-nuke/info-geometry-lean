# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:58.890801+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **66**
- Hard: **0**
- Soft: **22**
- Advisory: **44**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean` | `advisory` | 88 | 0 | 22 | 44 | 66 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauThermodynamics.lean`
- module: `InfoGeometry.Canonical.SouriauThermodynamics`
- status: `advisory`
- debt_score: `88`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field CartanSubalgebra.thermalElement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field ThermalRepresentation.character` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field ThermalRepresentation.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ThermalRepresentation.thermalElement` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L66 [soft] `law-field-locker` in `structure-field ThermalRepresentation.partitionFunction_eq_character` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L105 [soft] `law-field-locker` in `structure-field ClassicalMomentMap.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L126 [soft] `law-field-locker` in `structure-field QuantumRepresentationLayer.thermalGenerator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L127 [soft] `law-field-locker` in `structure-field QuantumRepresentationLayer.traceExists` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L149 [soft] `law-field-locker` in `structure-field WeightDecompositionWitness.weightSpace` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field SouriauMomentMap.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L166 [soft] `law-field-locker` in `structure-field SouriauMomentMap.number` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `skeletal-proof` in `theorem geometricTemperatureWeightPairing_eq_beta_mul_shiftedMomentReadout` — proof appears to close via minimal tactic one-liner
  - L268 [advisory] `existential-packaging` in `theorem souriauPartition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L277 [advisory] `existential-packaging` in `def souriauGibbsWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L287 [advisory] `existential-packaging` in `theorem souriauGibbsWeight_eq_density_div_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L299 [advisory] `existential-packaging` in `theorem souriauGibbsWeight_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L307 [advisory] `existential-packaging` in `theorem souriauGibbsWeight_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L315 [advisory] `existential-packaging` in `theorem souriauGibbsWeight_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L323 [advisory] `existential-packaging` in `def souriauMassieuPotential` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L330 [advisory] `existential-packaging` in `theorem souriauMassieuPotential_eq_log_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L338 [advisory] `existential-packaging` in `def souriauMeanShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L345 [advisory] `existential-packaging` in `def souriauMeanNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L354 [advisory] `existential-packaging` in `def souriauExpectedWeightPairing` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L362 [advisory] `existential-packaging` in `theorem souriauExpectedWeightPairing_eq_beta_mul_meanShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L379 [advisory] `existential-packaging` in `def souriauThermodynamicEntropy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L386 [advisory] `existential-packaging` in `theorem souriauThermodynamicEntropy_eq_massieu_add_beta_mul_meanShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L398 [advisory] `existential-packaging` in `def souriauFisherResponseMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L405 [advisory] `existential-packaging` in `def souriauFisherMetricMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L414 [advisory] `existential-packaging` in `theorem souriauFisher_betaBeta_eq_varianceShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L414 [soft] `skeletal-proof` in `theorem souriauFisher_betaBeta_eq_varianceShift` — proof appears to close via minimal tactic one-liner
  - L424 [advisory] `existential-packaging` in `theorem souriauFisher_betaBeta_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L433 [advisory] `existential-packaging` in `theorem souriauFisher_muMu_eq_beta_sq_varianceNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L433 [soft] `skeletal-proof` in `theorem souriauFisher_muMu_eq_beta_sq_varianceNumber` — proof appears to close via minimal tactic one-liner
  - L445 [advisory] `existential-packaging` in `theorem souriauFisher_muMu_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L455 [advisory] `existential-packaging` in `theorem souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L455 [soft] `skeletal-proof` in `theorem souriauFisher_betaMu_eq_meanNumber_sub_beta_mul_covariance` — proof appears to close via minimal tactic one-liner
  - L467 [advisory] `existential-packaging` in `theorem souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L467 [soft] `skeletal-proof` in `theorem souriauFisher_muBeta_eq_meanNumber_sub_beta_mul_covariance` — proof appears to close via minimal tactic one-liner
  - L479 [advisory] `existential-packaging` in `theorem souriauFisherResponseMatrix_symmetric` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L479 [soft] `skeletal-proof` in `theorem souriauFisherResponseMatrix_symmetric` — proof appears to close via minimal tactic one-liner
  - L488 [advisory] `existential-packaging` in `theorem souriauFisherMetricMatrix_isSymm` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L509 [advisory] `existential-packaging` in `theorem souriauFisherResponseMatrix_positiveSemidefinite_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L526 [advisory] `existential-packaging` in `def souriauFisherInverseMetricResponse` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L533 [advisory] `existential-packaging` in `def souriauFisherInverseMetricMatrix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L542 [advisory] `existential-packaging` in `theorem souriauFisherInverseMetricResponse_symmetric` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L551 [advisory] `existential-packaging` in `theorem souriauFisher_comp_inverseMetric_of_det_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L562 [advisory] `existential-packaging` in `theorem souriauFisher_inverseMetric_comp_of_det_ne_zero` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L576 [advisory] `existential-packaging` in `def souriauEntropyProduction` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L586 [advisory] `existential-packaging` in `theorem souriauEntropyProduction_nonneg_of_positiveSemidefinite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L586 [soft] `skeletal-proof` in `theorem souriauEntropyProduction_nonneg_of_positiveSemidefinite` — proof appears to close via minimal tactic one-liner
  - L603 [advisory] `existential-packaging` in `theorem souriauEntropyProduction_nonneg_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L621 [advisory] `existential-packaging` in `theorem souriauEntropyProduction_eq_zero_iff_force_zero_of_positiveDefinite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L621 [soft] `skeletal-proof` in `theorem souriauEntropyProduction_eq_zero_iff_force_zero_of_positiveDefinite` — proof appears to close via minimal tactic one-liner
  - L647 [advisory] `bridge-shaped-declaration` in `theorem souriauFisherOnsager_proof_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L647 [advisory] `existential-packaging` in `theorem souriauFisherOnsager_proof_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L674 [advisory] `existential-packaging` in `theorem souriau_beta_conjugate_shifted_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L674 [soft] `skeletal-proof` in `theorem souriau_beta_conjugate_shifted_readout` — proof appears to close via minimal tactic one-liner
  - L685 [advisory] `existential-packaging` in `theorem souriau_mu_conjugate_number_readout` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L685 [soft] `skeletal-proof` in `theorem souriau_mu_conjugate_number_readout` — proof appears to close via minimal tactic one-liner
  - L709 [advisory] `bridge-shaped-declaration` in `theorem gibbsSouriau_massieu_fisher_onsager_secondLaw_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L709 [advisory] `existential-packaging` in `theorem gibbsSouriau_massieu_fisher_onsager_secondLaw_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L746 [advisory] `existential-packaging` in `theorem souriau_canonical_hessian_eq_variance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L765 [advisory] `existential-packaging` in `def souriauPartitionAsCharacter` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L774 [advisory] `existential-packaging` in `theorem souriauPartitionAsCharacter_eq_souriauPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L774 [soft] `skeletal-proof` in `theorem souriauPartitionAsCharacter_eq_souriauPartition` — proof appears to close via minimal tactic one-liner

