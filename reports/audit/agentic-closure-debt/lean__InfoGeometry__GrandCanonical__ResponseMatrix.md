# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:40.639021+00:00`
Root: `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **9**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean` | `advisory` | 27 | 0 | 9 | 9 | 18 |

## Findings by file

### `lean/InfoGeometry/GrandCanonical/ResponseMatrix.lean`
- module: `InfoGeometry.GrandCanonical.ResponseMatrix`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L121 [soft] `skeletal-proof` in `lemma compose_inverseMetric_of_det_ne_zero` — proof appears to close via minimal tactic one-liner
  - L149 [soft] `skeletal-proof` in `lemma inverseMetric_compose_of_det_ne_zero` — proof appears to close via minimal tactic one-liner
  - L220 [soft] `skeletal-proof` in `theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite` — proof appears to close via minimal tactic one-liner
  - L231 [advisory] `local-hypothesis-injection` in `theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [advisory] `local-hypothesis-injection` in `theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [advisory] `local-hypothesis-injection` in `theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L241 [advisory] `local-hypothesis-injection` in `theorem entropyProduction_nonneg_of_symmetric_positiveSemidefinite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L281 [advisory] `local-hypothesis-injection` in `theorem entropyProduction_eq_zero_iff_force_zero_of_positiveDefinite` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L302 [soft] `skeletal-proof` in `lemma betaResponse_eq_neg_meanShift` — proof appears to close via minimal tactic one-liner
  - L309 [soft] `skeletal-proof` in `lemma muResponse_eq_beta_meanNumber` — proof appears to close via minimal tactic one-liner
  - L316 [soft] `skeletal-proof` in `theorem betaHessian_eq_varianceShift` — proof appears to close via minimal tactic one-liner
  - L330 [soft] `skeletal-proof` in `theorem muHessian_eq_beta_sq_varianceNumber` — proof appears to close via minimal tactic one-liner
  - L345 [soft] `skeletal-proof` in `theorem betaMuHessian_eq_meanNumber_sub_beta_mul_covariance` — proof appears to close via minimal tactic one-liner
  - L353 [soft] `skeletal-proof` in `theorem muBetaHessian_eq_meanNumber_sub_beta_mul_covariance` — proof appears to close via minimal tactic one-liner
  - L368 [advisory] `existential-packaging` in `theorem responseMatrix_symmetric_of_hessian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L376 [advisory] `existential-packaging` in `lemma responseMatrix_symmetric` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L392 [advisory] `existential-packaging` in `theorem responseMatrix_positiveSemidefinite_of_det_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

