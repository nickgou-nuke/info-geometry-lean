# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:57.394670+00:00`
Root: `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **7**
- Advisory: **18**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean` | `advisory` | 32 | 0 | 7 | 18 | 25 |

## Findings by file

### `lean/InfoGeometry/LLM/RouterFreeEnergyBridge.lean`
- module: `InfoGeometry.LLM.RouterFreeEnergyBridge`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `existential-packaging` in `theorem routerPartition_eq_finitePartition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L24 [soft] `skeletal-proof` in `theorem routerPartition_eq_finitePartition` — proof appears to close via minimal tactic one-liner
  - L32 [advisory] `existential-packaging` in `theorem normalizedWeights_eq_finite_gibbsWeight` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L32 [soft] `skeletal-proof` in `theorem normalizedWeights_eq_finite_gibbsWeight` — proof appears to close via minimal tactic one-liner
  - L38 [advisory] `existential-packaging` in `def routerInternalEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [advisory] `existential-packaging` in `def routerEntropy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L48 [advisory] `existential-packaging` in `def routerMassieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L53 [advisory] `existential-packaging` in `def routerFreeEnergy` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L61 [advisory] `existential-packaging` in `theorem routerMassieu_eq_logSumExpRouter` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L70 [advisory] `existential-packaging` in `theorem routerEntropy_eq_beta_internal_plus_massieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L70 [soft] `skeletal-proof` in `theorem routerEntropy_eq_beta_internal_plus_massieu` — proof appears to close via minimal tactic one-liner
  - L78 [advisory] `existential-packaging` in `theorem beta_mul_routerFreeEnergy_eq_neg_routerMassieu` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L78 [soft] `skeletal-proof` in `theorem beta_mul_routerFreeEnergy_eq_neg_routerMassieu` — proof appears to close via minimal tactic one-liner
  - L84 [advisory] `existential-packaging` in `def routerFreeEnergyEps` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L92 [advisory] `existential-packaging` in `theorem routerFreeEnergyEps_eq_neg_eps_logSumExpRouter` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L98 [advisory] `local-hypothesis-injection` in `theorem routerFreeEnergyEps_eq_neg_eps_logSumExpRouter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L110 [advisory] `existential-packaging` in `def routerScaledEntropicObjective` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L119 [advisory] `existential-packaging` in `def routerScaledPotentialGap` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L128 [soft] `simp-law-injection` in `simp-declaration routerScaledEntropicObjective_eq_scaledKL` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [advisory] `existential-packaging` in `theorem routerScaledEntropicObjective_eq_scaledKL` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L143 [soft] `simp-law-injection` in `simp-declaration routerScaledPotentialGap_eq_scaledBregman_swapped` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [advisory] `existential-packaging` in `theorem routerScaledPotentialGap_eq_scaledBregman_swapped` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L158 [soft] `simp-law-injection` in `simp-declaration routerScaledPotentialGap_eq_scaledBregman` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [advisory] `existential-packaging` in `theorem routerScaledPotentialGap_eq_scaledBregman` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

