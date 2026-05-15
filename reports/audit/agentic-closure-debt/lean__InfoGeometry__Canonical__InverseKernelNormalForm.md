# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:21.076410+00:00`
Root: `lean/InfoGeometry/Canonical/InverseKernelNormalForm.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/InverseKernelNormalForm.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/InverseKernelNormalForm.lean`
- module: `InfoGeometry.Canonical.InverseKernelNormalForm`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L81 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L91 [soft] `skeletal-proof` in `theorem chiralAnomaly_eq_zero_iff_spectralMetricCommute` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_zero_iff_spectralRangeCommute` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `skeletal-proof` in `theorem metricProjector_isSpectralCompact_of_spectralMetricCommute` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `skeletal-proof` in `theorem mpRangeProjector_isSpectralCompact_of_spectralRangeCommute` — proof appears to close via minimal tactic one-liner
  - L155 [soft] `skeletal-proof` in `theorem projectorMismatch_isSpectralCompact_of_spectralMetricCommute` — proof appears to close via minimal tactic one-liner
  - L178 [soft] `skeletal-proof` in `theorem dilationGap_isSpectralCompact_of_spectralMoorePenroseCommute` — proof appears to close via minimal tactic one-liner
  - L206 [soft] `skeletal-proof` in `theorem metricProjector_fixed_under_spectralGradingFlow_of_spectralMetricCommute` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `skeletal-proof` in `theorem mpRangeProjector_fixed_under_spectralGradingFlow_of_spectralRangeCommute` — proof appears to close via minimal tactic one-liner
  - L232 [soft] `skeletal-proof` in `theorem projectorMismatch_fixed_under_spectralGradingFlow_of_spectralMetricCommute` — proof appears to close via minimal tactic one-liner
  - L245 [soft] `skeletal-proof` in `theorem dilationGap_fixed_under_spectralGradingFlow_of_spectralMoorePenroseCommute` — proof appears to close via minimal tactic one-liner

