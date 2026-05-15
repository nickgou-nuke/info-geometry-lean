# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:39.111372+00:00`
Root: `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **46**
- Hard: **0**
- Soft: **17**
- Advisory: **29**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean` | `advisory` | 63 | 0 | 17 | 29 | 46 |

## Findings by file

### `lean/InfoGeometry/Canonical/AnalyticalIndexCore.lean`
- module: `InfoGeometry.Canonical.AnalyticalIndexCore`
- status: `advisory`
- debt_score: `63`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L115 [soft] `skeletal-proof` in `lemma chiralPartPlus_add_chiralPartMinus` — proof appears to close via minimal tactic one-liner
  - L123 [advisory] `local-hypothesis-injection` in `lemma chiralPartPlus_add_chiralPartMinus` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L141 [soft] `skeletal-proof` in `lemma chiralProjectorPlus_comp_self_of_square_eq_id` — proof appears to close via minimal tactic one-liner
  - L153 [advisory] `local-hypothesis-injection` in `lemma chiralProjectorPlus_comp_self_of_square_eq_id` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L167 [soft] `skeletal-proof` in `lemma chiralProjectorMinus_comp_self_of_square_eq_id` — proof appears to close via minimal tactic one-liner
  - L179 [advisory] `local-hypothesis-injection` in `lemma chiralProjectorMinus_comp_self_of_square_eq_id` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L193 [soft] `skeletal-proof` in `lemma chiralPartPlus_eq_projectorMinus_comp_of_anticommute` — proof appears to close via minimal tactic one-liner
  - L203 [advisory] `local-hypothesis-injection` in `lemma chiralPartPlus_eq_projectorMinus_comp_of_anticommute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [soft] `skeletal-proof` in `lemma chiralPartMinus_eq_projectorPlus_comp_of_anticommute` — proof appears to close via minimal tactic one-liner
  - L224 [advisory] `local-hypothesis-injection` in `lemma chiralPartMinus_eq_projectorPlus_comp_of_anticommute` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L265 [advisory] `local-hypothesis-injection` in `lemma analyticalIndex_eq_of_chiralParts_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L273 [advisory] `existential-packaging` in `def ChiralSliceIsoAlong` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L333 [advisory] `existential-packaging` in `def ChiralNoZeroCrossingNear` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L350 [advisory] `existential-packaging` in `def ChiralNoZeroEigenCrossingNear` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L381 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L383 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L385 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L390 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L397 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L399 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L401 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L406 [advisory] `local-hypothesis-injection` in `theorem chiralNoZeroCrossingNear_of_noZeroEigenCrossingNear` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L521 [soft] `skeletal-proof` in `lemma map_ker_eq_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L533 [advisory] `local-hypothesis-injection` in `lemma map_ker_eq_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L538 [advisory] `local-hypothesis-injection` in `lemma map_ker_eq_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L540 [advisory] `local-hypothesis-injection` in `lemma map_ker_eq_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L546 [soft] `skeletal-proof` in `lemma map_range_eq_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L559 [advisory] `local-hypothesis-injection` in `lemma map_range_eq_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L569 [soft] `skeletal-proof` in `lemma chiralProjectorPlus_comp_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L578 [advisory] `local-hypothesis-injection` in `lemma chiralProjectorPlus_comp_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L581 [soft] `skeletal-proof` in `lemma chiralProjectorMinus_comp_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L590 [advisory] `local-hypothesis-injection` in `lemma chiralProjectorMinus_comp_of_conjugacy` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L593 [soft] `skeletal-proof` in `lemma map_chiralKernelSlicePlus_eq_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L622 [soft] `skeletal-proof` in `lemma map_chiralKernelSliceMinus_eq_of_conjugacy` — proof appears to close via minimal tactic one-liner
  - L718 [soft] `skeletal-proof` in `theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport` — proof appears to close via minimal tactic one-liner
  - L744 [advisory] `local-hypothesis-injection` in `theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L761 [advisory] `local-hypothesis-injection` in `theorem chiralSliceIsoAlong_of_modularCliffordUnitTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L927 [soft] `simp-law-injection` in `simp-declaration KRotationLE_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L930 [soft] `simp-law-injection` in `simp-declaration KRotationLE_symm_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L957 [soft] `simp-law-injection` in `simp-declaration cartanConjugate_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L996 [soft] `skeletal-proof` in `theorem analyticalIndex_eq_zero_time_of_cartanConjugate` — proof appears to close via minimal tactic one-liner
  - L1047 [soft] `skeletal-proof` in `theorem cl11GlobalGrading_apply_tmul` — proof appears to close via minimal tactic one-liner
  - L1067 [advisory] `local-hypothesis-injection` in `theorem cl11BottDirac_comp_cl11GlobalGrading_add_cl11GlobalGrading_comp_cl11BottDirac` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1139 [advisory] `local-hypothesis-injection` in `theorem cl11GlobalGrading_comp_tensor_eq_tensor_comp_cl11GlobalGrading` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1157 [advisory] `local-hypothesis-injection` in `theorem cl11GlobalGrading_comp_tensor_modular_j_eq_tensor_comp_cl11GlobalGrading_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

