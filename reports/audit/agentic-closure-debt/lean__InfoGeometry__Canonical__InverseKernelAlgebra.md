# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:20.788171+00:00`
Root: `lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **11**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean` | `advisory` | 31 | 0 | 11 | 9 | 20 |

## Findings by file

### `lean/InfoGeometry/Canonical/InverseKernelAlgebra.lean`
- module: `InfoGeometry.Canonical.InverseKernelAlgebra`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L40 [soft] `skeletal-proof` in `theorem spectralProjector_add_spectralComplementaryProjector` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `theorem mpRangeProjector_add_mpRangeComplementaryProjector` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `theorem metricProjector_add_metricComplementaryProjector` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `skeletal-proof` in `theorem mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap` — proof appears to close via minimal tactic one-liner
  - L107 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L219 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_star_of_selfAdjoint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L222 [soft] `skeletal-proof` in `theorem mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap` — proof appears to close via minimal tactic one-liner
  - L229 [soft] `skeletal-proof` in `theorem projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `theorem rightProjectorMismatch_sub_projectorMismatch_eq_neg_two_smul_dilationGap` — proof appears to close via minimal tactic one-liner
  - L243 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange` — proof appears to close via minimal tactic one-liner
  - L252 [soft] `skeletal-proof` in `theorem spectralProjector_mul_chiralAnomaly_mul_spectralProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L261 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_mul_chiralAnomaly_mul_spectralProjector_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L271 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L281 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L283 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L288 [advisory] `local-hypothesis-injection` in `theorem spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L299 [soft] `skeletal-proof` in `theorem chiralAnomaly_eq_offDiagonal_spectralSplit` — proof appears to close via minimal tactic one-liner
  - L310 [advisory] `local-hypothesis-injection` in `theorem chiralAnomaly_eq_offDiagonal_spectralSplit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

