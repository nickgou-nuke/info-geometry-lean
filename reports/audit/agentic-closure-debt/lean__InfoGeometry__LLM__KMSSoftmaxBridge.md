# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:56.324766+00:00`
Root: `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **22**
- Hard: **0**
- Soft: **9**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean` | `advisory` | 31 | 0 | 9 | 13 | 22 |

## Findings by file

### `lean/InfoGeometry/LLM/KMSSoftmaxBridge.lean`
- module: `InfoGeometry.LLM.KMSSoftmaxBridge`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `existential-packaging` in `def softmaxWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L21 [advisory] `existential-packaging` in `def kmsWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L27 [advisory] `existential-packaging` in `def routerLogit` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L33 [soft] `simp-law-injection` in `simp-declaration softmaxWeight_eq_kmsWeight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [advisory] `existential-packaging` in `theorem softmaxWeight_eq_kmsWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L41 [soft] `simp-law-injection` in `simp-declaration softmaxWeight_eq_exp_routerLogit_div_partition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [advisory] `existential-packaging` in `theorem softmaxWeight_eq_exp_routerLogit_div_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L44 [soft] `skeletal-proof` in `theorem softmaxWeight_eq_exp_routerLogit_div_partition` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `simp-law-injection` in `simp-declaration kmsWeight_sum_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [advisory] `existential-packaging` in `theorem kmsWeight_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L61 [soft] `simp-law-injection` in `simp-declaration softmaxWeight_sum_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L64 [advisory] `existential-packaging` in `theorem softmaxWeight_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [soft] `skeletal-proof` in `theorem softmaxWeight_sum_one` — proof appears to close via minimal tactic one-liner
  - L70 [advisory] `existential-packaging` in `def kmsLogPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L75 [soft] `simp-law-injection` in `simp-declaration kmsLogPartition_eq_logSumExpRouter` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [advisory] `existential-packaging` in `theorem kmsLogPartition_eq_logSumExpRouter` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L86 [advisory] `existential-packaging` in `theorem kmsEntropy_eq_beta_internal_plus_logPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L86 [soft] `skeletal-proof` in `theorem kmsEntropy_eq_beta_internal_plus_logPartition` — proof appears to close via minimal tactic one-liner
  - L95 [advisory] `existential-packaging` in `theorem beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L95 [soft] `skeletal-proof` in `theorem beta_mul_routerFreeEnergy_eq_neg_kmsLogPartition` — proof appears to close via minimal tactic one-liner
  - L105 [advisory] `existential-packaging` in `theorem routerFreeEnergyEps_eq_neg_eps_kmsLogPartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

