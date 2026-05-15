# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:40.520287+00:00`
Root: `lean/InfoGeometry/GrandCanonical/Core.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **69**
- Hard: **0**
- Soft: **17**
- Advisory: **52**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GrandCanonical/Core.lean` | `advisory` | 86 | 0 | 17 | 52 | 69 |

## Findings by file

### `lean/InfoGeometry/GrandCanonical/Core.lean`
- module: `InfoGeometry.GrandCanonical.Core`
- status: `advisory`
- debt_score: `86`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [advisory] `existential-packaging` in `structure GrandCanonicalParams` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L21 [soft] `law-field-locker` in `structure-field GrandCanonicalParams.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [advisory] `existential-packaging` in `def secondMoment` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L103 [soft] `skeletal-proof` in `lemma hasDerivAt_exp_neg_mul_energy` — proof appears to close via minimal tactic one-liner
  - L109 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_exp_neg_mul_energy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L114 [advisory] `existential-packaging` in `def partitionDerivFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L121 [advisory] `existential-packaging` in `lemma partitionDerivFun_eq_neg_firstMoment` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [advisory] `existential-packaging` in `lemma hasDerivAt_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `skeletal-proof` in `lemma hasDerivAt_partition` — proof appears to close via minimal tactic one-liner
  - L144 [advisory] `existential-packaging` in `lemma deriv_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L150 [advisory] `existential-packaging` in `lemma hasDerivAt_partitionDerivTerm` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L160 [advisory] `existential-packaging` in `lemma hasDerivAt_partitionDerivFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L160 [soft] `skeletal-proof` in `lemma hasDerivAt_partitionDerivFun` — proof appears to close via minimal tactic one-liner
  - L180 [soft] `skeletal-proof` in `lemma potential_deriv_eq_partitionDeriv_div_partition` — proof appears to close via minimal tactic one-liner
  - L257 [soft] `skeletal-proof` in `lemma variance_eq_zero_iff_energy_eq_mean` — proof appears to close via minimal tactic one-liner
  - L268 [advisory] `local-hypothesis-injection` in `lemma variance_eq_zero_iff_energy_eq_mean` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L271 [advisory] `local-hypothesis-injection` in `lemma variance_eq_zero_iff_energy_eq_mean` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L274 [advisory] `local-hypothesis-injection` in `lemma variance_eq_zero_iff_energy_eq_mean` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L277 [advisory] `local-hypothesis-injection` in `lemma variance_eq_zero_iff_energy_eq_mean` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L371 [advisory] `local-hypothesis-injection` in `lemma hessian_eq_secondMoment_sub_mean_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L373 [advisory] `local-hypothesis-injection` in `lemma hessian_eq_secondMoment_sub_mean_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L375 [advisory] `local-hypothesis-injection` in `lemma hessian_eq_secondMoment_sub_mean_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L405 [advisory] `existential-packaging` in `structure GrandCanonicalTwoParam` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L410 [soft] `law-field-locker` in `structure-field GrandCanonicalTwoParam.energy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L411 [soft] `law-field-locker` in `structure-field GrandCanonicalTwoParam.number` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L565 [advisory] `existential-packaging` in `def covarianceShiftNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L575 [soft] `skeletal-proof` in `lemma hasDerivAt_exp_neg_mul_shiftedEnergy_beta` — proof appears to close via minimal tactic one-liner
  - L587 [advisory] `existential-packaging` in `def partitionGCDerivBetaFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L594 [advisory] `existential-packaging` in `lemma partitionGCDerivBetaFun_eq_neg_firstShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L601 [soft] `skeletal-proof` in `lemma hasDerivAt_partitionGC_beta` — proof appears to close via minimal tactic one-liner
  - L615 [soft] `skeletal-proof` in `lemma potentialGC_deriv_beta_eq_partitionDeriv_div_partition` — proof appears to close via minimal tactic one-liner
  - L621 [advisory] `local-hypothesis-injection` in `lemma potentialGC_deriv_beta_eq_partitionDeriv_div_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L654 [advisory] `existential-packaging` in `lemma potentialGC_deriv_beta_eq_neg_meanShift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L664 [soft] `skeletal-proof` in `lemma hasDerivAt_exp_neg_mul_shiftedEnergy_mu` — proof appears to close via minimal tactic one-liner
  - L670 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_exp_neg_mul_shiftedEnergy_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L673 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_exp_neg_mul_shiftedEnergy_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L684 [advisory] `existential-packaging` in `def partitionGCDerivMuFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L691 [advisory] `existential-packaging` in `lemma partitionGCDerivMuFun_eq_beta_mul_firstNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L710 [soft] `skeletal-proof` in `lemma hasDerivAt_partitionGC_mu` — proof appears to close via minimal tactic one-liner
  - L724 [soft] `skeletal-proof` in `lemma potentialGC_deriv_mu_eq_partitionDeriv_div_partition` — proof appears to close via minimal tactic one-liner
  - L730 [advisory] `local-hypothesis-injection` in `lemma potentialGC_deriv_mu_eq_partitionDeriv_div_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L971 [advisory] `existential-packaging` in `lemma potentialGC_deriv_mu_eq_beta_meanNumber` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L982 [advisory] `existential-packaging` in `lemma hasDerivAt_firstShiftUnnormalized_beta_term` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L995 [advisory] `existential-packaging` in `lemma hasDerivAt_firstShiftUnnormalized_beta` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1008 [advisory] `existential-packaging` in `lemma deriv_firstShiftUnnormalized_beta` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1016 [advisory] `existential-packaging` in `lemma hasDerivAt_firstNumberUnnormalized_beta_term` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1029 [advisory] `existential-packaging` in `lemma hasDerivAt_firstNumberUnnormalized_beta` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1042 [advisory] `existential-packaging` in `lemma deriv_firstNumberUnnormalized_beta` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1050 [advisory] `existential-packaging` in `lemma hasDerivAt_firstNumberUnnormalized_mu_term` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1063 [advisory] `existential-packaging` in `lemma hasDerivAt_firstNumberUnnormalized_mu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1076 [advisory] `existential-packaging` in `lemma deriv_firstNumberUnnormalized_mu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1084 [advisory] `existential-packaging` in `lemma hasDerivAt_firstShiftUnnormalized_mu_term` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1084 [soft] `skeletal-proof` in `lemma hasDerivAt_firstShiftUnnormalized_mu_term` — proof appears to close via minimal tactic one-liner
  - L1093 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_firstShiftUnnormalized_mu_term` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1096 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_firstShiftUnnormalized_mu_term` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1106 [advisory] `existential-packaging` in `lemma hasDerivAt_firstShiftUnnormalized_mu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L1138 [advisory] `local-hypothesis-injection` in `lemma deriv_meanShift_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1141 [advisory] `local-hypothesis-injection` in `lemma deriv_meanShift_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1181 [advisory] `local-hypothesis-injection` in `lemma deriv_meanNumber_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1184 [advisory] `local-hypothesis-injection` in `lemma deriv_meanNumber_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1223 [advisory] `local-hypothesis-injection` in `lemma deriv_meanNumber_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1226 [advisory] `local-hypothesis-injection` in `lemma deriv_meanNumber_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1268 [advisory] `local-hypothesis-injection` in `lemma deriv_meanShift_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1271 [advisory] `local-hypothesis-injection` in `lemma deriv_meanShift_mu` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1300 [soft] `skeletal-proof` in `theorem potentialGC_hessian_beta_beta` — proof appears to close via minimal tactic one-liner
  - L1337 [soft] `skeletal-proof` in `theorem potentialGC_hessian_beta_mu` — proof appears to close via minimal tactic one-liner
  - L1372 [advisory] `local-hypothesis-injection` in `theorem potentialGC_hessian_mu_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1397 [advisory] `local-hypothesis-injection` in `theorem potentialGC_hessian_mu_beta` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

