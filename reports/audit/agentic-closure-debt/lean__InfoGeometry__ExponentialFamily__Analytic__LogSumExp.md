# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:28.957516+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **40**
- Hard: **0**
- Soft: **15**
- Advisory: **25**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean` | `advisory` | 55 | 0 | 15 | 25 | 40 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Analytic/LogSumExp.lean`
- module: `InfoGeometry.ExponentialFamily.Analytic.LogSumExp`
- status: `advisory`
- debt_score: `55`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L115 [soft] `simp-law-injection` in `simp-declaration logSumExpScaledEntropicTransportObjective_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration logSumExpScaledEntropicTransportPotentialGap_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [advisory] `existential-packaging` in `lemma logSumExp_sum_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L145 [advisory] `existential-packaging` in `lemma logSumExpScaledPartition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L145 [soft] `skeletal-proof` in `lemma logSumExpScaledPartition_pos` — proof appears to close via minimal tactic one-liner
  - L154 [advisory] `existential-packaging` in `lemma logSumExpWeight_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L176 [advisory] `existential-packaging` in `lemma logSumExpWeight_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L187 [advisory] `existential-packaging` in `lemma logSumExpScaledWeight_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L187 [soft] `skeletal-proof` in `lemma logSumExpScaledWeight_sum_one` — proof appears to close via minimal tactic one-liner
  - L196 [advisory] `existential-packaging` in `lemma logSumExpScaledWeight_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L196 [soft] `skeletal-proof` in `lemma logSumExpScaledWeight_pos` — proof appears to close via minimal tactic one-liner
  - L205 [soft] `skeletal-proof` in `lemma hasDerivAt_logSumExpPartition_term` — proof appears to close via minimal tactic one-liner
  - L213 [advisory] `local-hypothesis-injection` in `lemma hasDerivAt_logSumExpPartition_term` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L266 [advisory] `existential-packaging` in `lemma logSumExpMean_eq_weighted_sum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L266 [soft] `skeletal-proof` in `lemma logSumExpMean_eq_weighted_sum` — proof appears to close via minimal tactic one-liner
  - L290 [advisory] `existential-packaging` in `lemma logSumExpSecondMoment_eq_weighted_sum` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L290 [soft] `skeletal-proof` in `lemma logSumExpSecondMoment_eq_weighted_sum` — proof appears to close via minimal tactic one-liner
  - L315 [advisory] `existential-packaging` in `lemma logSumExp_deriv_eq_ratio` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L315 [soft] `skeletal-proof` in `lemma logSumExp_deriv_eq_ratio` — proof appears to close via minimal tactic one-liner
  - L334 [advisory] `existential-packaging` in `lemma logSumExp_deriv_eq_mean` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L334 [soft] `skeletal-proof` in `lemma logSumExp_deriv_eq_mean` — proof appears to close via minimal tactic one-liner
  - L342 [advisory] `existential-packaging` in `lemma logSumExp_secondDeriv_eq_ratio` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L381 [advisory] `existential-packaging` in `lemma logSumExp_secondDeriv_eq_variance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L393 [advisory] `existential-packaging` in `lemma logSumExpScaledMean_eq_eps_mul_mean` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L393 [soft] `skeletal-proof` in `lemma logSumExpScaledMean_eq_eps_mul_mean` — proof appears to close via minimal tactic one-liner
  - L423 [advisory] `existential-packaging` in `lemma logSumExpScaled_deriv_eq_mean` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L443 [advisory] `existential-packaging` in `lemma logSumExpScaled_logWeight_eq` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L477 [advisory] `existential-packaging` in `lemma logSumExpScaledKL_eq` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L534 [advisory] `existential-packaging` in `lemma logSumExpScaledKL_eq_inv_eps_mul_gap` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L551 [advisory] `existential-packaging` in `lemma logSumExpScaledKL_eq_inv_eps_mul_bregman` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L566 [advisory] `existential-packaging` in `lemma logSumExpScaledBregman_eq_eps_mul_KL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L566 [soft] `skeletal-proof` in `lemma logSumExpScaledBregman_eq_eps_mul_KL` — proof appears to close via minimal tactic one-liner
  - L588 [advisory] `existential-packaging` in `lemma logSumExpScaledEntropicTransportObjective_eq_inv_eps_mul_potentialGap` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L588 [soft] `skeletal-proof` in `lemma logSumExpScaledEntropicTransportObjective_eq_inv_eps_mul_potentialGap` — proof appears to close via minimal tactic one-liner
  - L600 [advisory] `existential-packaging` in `lemma logSumExpScaledEntropicTransportPotentialGap_eq_eps_mul_objective` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L600 [soft] `skeletal-proof` in `lemma logSumExpScaledEntropicTransportPotentialGap_eq_eps_mul_objective` — proof appears to close via minimal tactic one-liner
  - L612 [advisory] `existential-packaging` in `lemma logSumExp_contDiff` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L612 [soft] `skeletal-proof` in `lemma logSumExp_contDiff` — proof appears to close via minimal tactic one-liner
  - L624 [advisory] `local-hypothesis-injection` in `lemma logSumExp_contDiff` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

