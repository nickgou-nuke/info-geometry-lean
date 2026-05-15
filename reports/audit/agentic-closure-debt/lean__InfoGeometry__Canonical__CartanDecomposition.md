# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:48.644618+00:00`
Root: `lean/InfoGeometry/Canonical/CartanDecomposition.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **14**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CartanDecomposition.lean` | `advisory` | 38 | 0 | 14 | 10 | 24 |

## Findings by file

### `lean/InfoGeometry/Canonical/CartanDecomposition.lean`
- module: `InfoGeometry.Canonical.CartanDecomposition`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L83 [advisory] `local-hypothesis-injection` in `theorem GammaS_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [advisory] `local-hypothesis-injection` in `theorem GammaS_mul_spectralProjector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `local-hypothesis-injection` in `theorem spectralProjector_mul_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L119 [advisory] `local-hypothesis-injection` in `theorem GammaS_mul_spectralComplement` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L131 [advisory] `local-hypothesis-injection` in `theorem spectralComplement_mul_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [soft] `skeletal-proof` in `theorem thetaS_involutive` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem isSpectralCompact_iff_commute` — proof appears to close via minimal tactic one-liner
  - L212 [soft] `skeletal-proof` in `theorem isSpectralNonCompact_iff_anticommute` — proof appears to close via minimal tactic one-liner
  - L254 [soft] `skeletal-proof` in `theorem spectralCommutator_mem_compact` — proof appears to close via minimal tactic one-liner
  - L275 [soft] `skeletal-proof` in `theorem spectralCommutator_compact_noncompact` — proof appears to close via minimal tactic one-liner
  - L300 [soft] `skeletal-proof` in `theorem spectralCommutator_mem_compact_of_noncompact` — proof appears to close via minimal tactic one-liner
  - L337 [soft] `skeletal-proof` in `theorem spectral_proj_is_compact_of_normal` — proof appears to close via minimal tactic one-liner
  - L356 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L365 [advisory] `local-hypothesis-injection` in `lemma smul_pow_even_of_sq_eq_one` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L435 [soft] `skeletal-proof` in `theorem spectralGradingFlow_add` — proof appears to close via minimal tactic one-liner
  - L443 [soft] `skeletal-proof` in `theorem spectralGradingFlow_zero` — proof appears to close via minimal tactic one-liner
  - L485 [soft] `skeletal-proof` in `theorem spectralGradingFlow_mem_compact` — proof appears to close via minimal tactic one-liner
  - L495 [soft] `skeletal-proof` in `theorem commute_spectralGradingFlow_of_commute_GammaS` — proof appears to close via minimal tactic one-liner
  - L503 [soft] `skeletal-proof` in `theorem spectralAdjointFlow_eq_self_of_commute_GammaS` — proof appears to close via minimal tactic one-liner
  - L671 [soft] `skeletal-proof` in `theorem mul_spectralGradingFlow_eq_spectralGradingFlow_neg_mul_of_anticommute_GammaS` — proof appears to close via minimal tactic one-liner
  - L696 [soft] `skeletal-proof` in `theorem spectralGradingFlow_mul_eq_mul_spectralGradingFlow_neg_of_anticommute_GammaS` — proof appears to close via minimal tactic one-liner
  - L707 [advisory] `local-hypothesis-injection` in `theorem spectralGradingFlow_mul_eq_mul_spectralGradingFlow_neg_of_anticommute_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

