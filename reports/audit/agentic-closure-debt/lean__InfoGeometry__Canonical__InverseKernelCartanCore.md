# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:20.936503+00:00`
Root: `lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **15**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean` | `advisory` | 33 | 0 | 15 | 3 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/InverseKernelCartanCore.lean`
- module: `InfoGeometry.Canonical.InverseKernelCartanCore`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L31 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `skeletal-proof` in `theorem GammaS_eq_two_mul_spectralProjector_sub_one` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem GammaS_sq_eq_one` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `skeletal-proof` in `theorem GammaS_mul_spectralProjector` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `skeletal-proof` in `theorem thetaS_involutive` — proof appears to close via minimal tactic one-liner
  - L111 [soft] `skeletal-proof` in `theorem isSpectralCompact_iff_commute_GammaS` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem isSpectralNonCompact_iff_anticommute_GammaS` — proof appears to close via minimal tactic one-liner
  - L127 [soft] `skeletal-proof` in `theorem spectralProjector_isSpectralCompact` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_isSpectralCompact` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem spectralGradingFlow_add` — proof appears to close via minimal tactic one-liner
  - L151 [soft] `skeletal-proof` in `theorem spectralGradingFlow_zero` — proof appears to close via minimal tactic one-liner
  - L158 [soft] `skeletal-proof` in `theorem spectralGradingFlow_eq_cosh_add_sinh_GammaS` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `skeletal-proof` in `theorem spectralProjector_commutes_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L176 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_commutes_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L185 [soft] `skeletal-proof` in `theorem spectralProjector_fixed_under_spectralGradingFlow` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem spectralComplementaryProjector_fixed_under_spectralGradingFlow` — proof appears to close via minimal tactic one-liner

