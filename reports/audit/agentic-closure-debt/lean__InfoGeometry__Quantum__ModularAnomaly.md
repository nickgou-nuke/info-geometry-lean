# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:35.584231+00:00`
Root: `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **68**
- Hard: **0**
- Soft: **40**
- Advisory: **28**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/ModularAnomaly.lean` | `advisory` | 108 | 0 | 40 | 28 | 68 |

## Findings by file

### `lean/InfoGeometry/Quantum/ModularAnomaly.lean`
- module: `InfoGeometry.Quantum.ModularAnomaly`
- status: `advisory`
- debt_score: `108`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `law-field-locker` in `structure-field TopologicalMajoranaShadow.sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field TopologicalMajoranaShadow.sigma_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field TopologicalMajoranaShadow.sigma_add` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field TopologicalMajoranaShadow.J_conj_sigma` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L61 [soft] `skeletal-proof` in `lemma sigma_zero_clm` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `theorem hasDerivAt_modularCocycle_inner` — proof appears to close via minimal tactic one-liner
  - L90 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L92 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L93 [soft] `skeletal-proof` in `theorem modularAnomalyGenerator_eq_commutator_shadow` — proof appears to close via minimal tactic one-liner
  - L125 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L127 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L128 [advisory] `bridge-shaped-declaration` in `theorem unified_anomaly_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L128 [soft] `skeletal-proof` in `theorem unified_anomaly_bridge` — proof appears to close via minimal tactic one-liner
  - L185 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L238 [soft] `simp-law-injection` in `simp-declaration expFlow_toContinuousLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L243 [soft] `simp-law-injection` in `simp-declaration expFlow_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L250 [soft] `skeletal-proof` in `theorem expFlow_add` — proof appears to close via minimal tactic one-liner
  - L291 [soft] `skeletal-proof` in `theorem modularAnomalyGenerator_eq_exp_commutator_shadow` — proof appears to close via minimal tactic one-liner
  - L320 [advisory] `local-hypothesis-injection` in `theorem modularAnomalyGenerator_eq_exp_commutator_shadow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L323 [advisory] `local-hypothesis-injection` in `theorem modularAnomalyGenerator_eq_exp_commutator_shadow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L366 [soft] `simp-law-injection` in `simp-declaration canonicalCl11Generator_eq_spectral_epsilon` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L415 [soft] `skeletal-proof` in `theorem modularAnomalyGenerator_eq_canonicalCl11_commutator_shadow` — proof appears to close via minimal tactic one-liner
  - L473 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_id` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L475 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_id` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L542 [soft] `skeletal-proof` in `theorem expFlow_modular_j_eq_sigmaMap` — proof appears to close via minimal tactic one-liner
  - L549 [soft] `skeletal-proof` in `lemma hasDerivAt_sigmaMap_zero` — proof appears to close via minimal tactic one-liner
  - L563 [soft] `skeletal-proof` in `lemma hasDerivAt_sigmaMap_neg_zero` — proof appears to close via minimal tactic one-liner
  - L576 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_sigmaMap_neg_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L578 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_sigmaMap_neg_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L707 [advisory] `local-hypothesis-injection` in `theorem latticeAnomalyCommutator_eq_zero_iff_blocks_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L714 [advisory] `local-hypothesis-injection` in `theorem latticeAnomalyCommutator_eq_zero_iff_blocks_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L720 [advisory] `local-hypothesis-injection` in `theorem latticeAnomalyCommutator_eq_zero_iff_blocks_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L726 [soft] `skeletal-proof` in `lemma bogoliubov_ortho_blocks_11` — proof appears to close via minimal tactic one-liner
  - L763 [advisory] `local-hypothesis-injection` in `theorem anomaly_free_blockA_is_orthogonal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L778 [soft] `simp-law-injection` in `simp-declaration blockA_sigmaMatrix` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L782 [soft] `simp-law-injection` in `simp-declaration blockB_sigmaMatrix` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L786 [soft] `simp-law-injection` in `simp-declaration blockC_sigmaMatrix` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L790 [soft] `simp-law-injection` in `simp-declaration blockD_sigmaMatrix` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L810 [soft] `skeletal-proof` in `theorem wittenIndex_sigmaMatrix` — proof appears to close via minimal tactic one-liner
  - L822 [advisory] `local-hypothesis-injection` in `theorem wittenIndex_sigmaMatrix_eq_one_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L823 [advisory] `local-hypothesis-injection` in `theorem wittenIndex_sigmaMatrix_eq_one_iff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L828 [soft] `skeletal-proof` in `theorem det_sigmaMatrix` — proof appears to close via minimal tactic one-liner
  - L833 [advisory] `local-hypothesis-injection` in `theorem det_sigmaMatrix` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L854 [advisory] `local-hypothesis-injection` in `theorem det_sigmaMatrix` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L921 [advisory] `local-hypothesis-injection` in `instance sigmaMatrix_blockD_invertible` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L934 [soft] `skeletal-proof` in `theorem schurDet_eq_det` — proof appears to close via minimal tactic one-liner
  - L980 [advisory] `local-hypothesis-injection` in `theorem thermal_berezinian_index` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L981 [advisory] `local-hypothesis-injection` in `theorem thermal_berezinian_index` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L988 [advisory] `local-hypothesis-injection` in `theorem thermal_berezinian_index` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1058 [soft] `simp-law-injection` in `simp-declaration latticeCoordEquiv_to_doubled_apply_inl` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1063 [soft] `simp-law-injection` in `simp-declaration latticeCoordEquiv_to_doubled_apply_inr` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1068 [soft] `simp-law-injection` in `simp-declaration latticeCoordEquiv_symm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1096 [soft] `simp-law-injection` in `simp-declaration coe_latticeAvatarCLM` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1102 [soft] `simp-law-injection` in `simp-declaration latticeAvatarCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1108 [soft] `simp-law-injection` in `simp-declaration latticeAvatarCLM_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1115 [soft] `simp-law-injection` in `simp-declaration latticeAvatarCLM_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1130 [soft] `simp-law-injection` in `simp-declaration latticeMatrixCLM_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1144 [soft] `simp-law-injection` in `simp-declaration latticeAutomorphismAvatar_symm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1151 [soft] `simp-law-injection` in `simp-declaration latticeAutomorphismAvatar_toContinuousLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1177 [soft] `simp-law-injection` in `simp-declaration jMatrix_mulVec_inl` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1182 [soft] `simp-law-injection` in `simp-declaration jMatrix_mulVec_inr` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L1247 [soft] `skeletal-proof` in `theorem latticeAvatar_modular_j` — proof appears to close via minimal tactic one-liner
  - L1263 [advisory] `local-hypothesis-injection` in `theorem latticeAvatar_sigmaMap_modularConjugationJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1274 [advisory] `local-hypothesis-injection` in `theorem latticeAvatar_sigmaMap_modularConjugationJ` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1350 [soft] `skeletal-proof` in `theorem latticeAvatar_sigmaMap_modular_j` — proof appears to close via minimal tactic one-liner
  - L1372 [soft] `skeletal-proof` in `theorem latticeAvatar_exp_modular_j` — proof appears to close via minimal tactic one-liner

