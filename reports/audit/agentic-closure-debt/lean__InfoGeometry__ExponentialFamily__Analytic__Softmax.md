# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:29.087330+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **10**
- Advisory: **11**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean` | `advisory` | 31 | 0 | 10 | 11 | 21 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Analytic/Softmax.lean`
- module: `InfoGeometry.ExponentialFamily.Analytic.Softmax`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `existential-packaging` in `abbrev secondMomentUnnormalized` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L40 [soft] `skeletal-proof` in `lemma softmaxPartition_pos` — proof appears to close via minimal tactic one-liner
  - L45 [soft] `skeletal-proof` in `lemma softmaxProb_pos` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `lemma softmaxProb_sum_one` — proof appears to close via minimal tactic one-liner
  - L62 [advisory] `local-hypothesis-injection` in `def softmaxDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L65 [advisory] `local-hypothesis-injection` in `def softmaxDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L78 [soft] `simp-law-injection` in `simp-declaration softmaxDist_prob_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [advisory] `local-hypothesis-injection` in `def softmaxDist` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `existential-packaging` in `lemma softmaxVariance_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L108 [advisory] `local-hypothesis-injection` in `lemma softmaxVariance_nonneg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L113 [soft] `skeletal-proof` in `lemma hasDerivAt_softmaxPartition` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `lemma deriv_softmaxPartition` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `lemma hasDerivAt_firstMomentUnnormalized` — proof appears to close via minimal tactic one-liner
  - L131 [soft] `skeletal-proof` in `lemma deriv_firstMomentUnnormalized` — proof appears to close via minimal tactic one-liner
  - L137 [advisory] `existential-packaging` in `lemma logSumExp_eq_log_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L137 [soft] `skeletal-proof` in `lemma logSumExp_eq_log_partition` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `lemma deriv_logSumExp_eq_firstMoment_div_partition` — proof appears to close via minimal tactic one-liner
  - L226 [advisory] `local-hypothesis-injection` in `lemma softmaxVariance_eq_secondMoment_sub_mean_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L229 [advisory] `local-hypothesis-injection` in `lemma softmaxVariance_eq_secondMoment_sub_mean_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L247 [advisory] `existential-packaging` in `theorem deriv2_logSumExp_eq_softmaxVariance` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

