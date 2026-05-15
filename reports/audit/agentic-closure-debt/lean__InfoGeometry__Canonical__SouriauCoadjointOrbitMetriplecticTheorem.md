# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.383135+00:00`
Root: `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **83**
- Hard: **0**
- Soft: **68**
- Advisory: **15**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean` | `advisory` | 151 | 0 | 68 | 15 | 83 |

## Findings by file

### `lean/InfoGeometry/Canonical/SouriauCoadjointOrbitMetriplecticTheorem.lean`
- module: `InfoGeometry.Canonical.SouriauCoadjointOrbitMetriplecticTheorem`
- status: `advisory`
- debt_score: `151`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.isOnCoadjointOrbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.reversibleVectorField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.metricVectorField` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.reversibleEntropyRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.metricEntropyRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.totalEntropyRate` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.moment_mem_orbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.reversible_preserves_orbit` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.metric_preserves_state` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.casimir_reversible` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.onsager_metric_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitMetriplecticContext.total_entropy_split` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L99 [advisory] `existential-packaging` in `def ofMomentImage` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L169 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L169 [soft] `section-law-variable` in `variable moment` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L176 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L186 [soft] `skeletal-proof` in `theorem reversibleEntropyRate_eq_zero` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `theorem metricEntropyRate_eq_square` — proof appears to close via minimal tactic one-liner
  - L200 [soft] `skeletal-proof` in `theorem totalEntropyRate_eq_square` — proof appears to close via minimal tactic one-liner
  - L281 [advisory] `bridge-shaped-declaration` in `theorem casimir_leaf_transverse_onsager_square_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L416 [advisory] `existential-packaging` in `theorem ofMomentImage_full_coadjoint_orbit_metriplectic_theorem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L466 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L468 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L470 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.massieuPotential` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L472 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.thermodynamicMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L474 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fisherHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L476 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.momentCovariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L478 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.nonzeroTangent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L480 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.souriauEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L482 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.betaOfMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L484 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.entropyHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L486 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.inverseFisherHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L488 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.massieu_eq_log_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L492 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.first_variation_eq_moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L497 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.second_variation_eq_fisher` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L502 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fisher_eq_covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L506 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fisher_symmetric` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L511 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fisher_nonnegative` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L515 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fisher_positive_of_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L519 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.fenchel_legendre_contact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L524 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.entropy_gradient_eq_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L529 [soft] `law-field-locker` in `structure-field InfiniteCoadjointOrbitHessianContext.entropy_hessian_eq_inverse_fisher` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L753 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L755 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.integralFunctional` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L757 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.gibbsWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L759 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.centeredMomentFeature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L761 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L765 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.thermodynamicMoment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L767 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.souriauEntropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L769 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.entropyGradient` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L773 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.feature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L775 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.partition_eq_integral_gibbsWeight` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L779 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.massieu_eq_log_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L783 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.thermodynamicMoment_eq_gradient_at_beta` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L787 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.entropyGradient_at_moment` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L791 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.fisherEquiv_eq_massieuHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L795 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.entropyGradient_derivative_eq_inverse` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L800 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.fisherEquiv_eq_gram` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L804 [soft] `law-field-locker` in `structure-field GibbsSouriauGramAnalyticWitness.fisherEquiv_eq_integral_centered_moment_product` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L836 [advisory] `bridge-shaped-declaration` in `theorem integral_covariance_gram_legendre_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1079 [soft] `law-field-locker` in `structure-field SmoothLegendreGramOwner.feature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1080 [soft] `law-field-locker` in `structure-field SmoothLegendreGramOwner.fisher_eq_gram` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1082 [soft] `law-field-locker` in `structure-field SmoothLegendreGramOwner.feature_nonzero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1104 [advisory] `bridge-shaped-declaration` in `theorem constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1116 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.partitionFunction` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1117 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.fisherHessian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1118 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.momentCovariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1121 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.context_partition` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1122 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.context_fisher` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1123 [soft] `law-field-locker` in `structure-field LogPartitionFisherCovarianceOwner.context_covariance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1137 [advisory] `bridge-shaped-declaration` in `theorem massieu_log_partition_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1144 [advisory] `bridge-shaped-declaration` in `theorem fisher_covariance_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1151 [advisory] `bridge-shaped-declaration` in `theorem constructive_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1324 [soft] `law-field-locker` in `structure-field SmoothLegendreInverseWitness.fisher_readout_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1329 [soft] `law-field-locker` in `structure-field SmoothLegendreInverseWitness.entropy_readout_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1334 [soft] `law-field-locker` in `structure-field SmoothLegendreInverseWitness.inverse_readout_matches` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L1380 [advisory] `bridge-shaped-declaration` in `theorem souriau_inverse_fisher_from_smooth_legendre_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L1938 [advisory] `bridge-shaped-declaration` in `theorem fisher_onsager_metriplectic_constructive_proof_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L2023 [advisory] `bridge-shaped-declaration` in `theorem gibbs_souriau_integral_covariance_to_metriplectic_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

