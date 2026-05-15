# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.772851+00:00`
Root: `lean/InfoGeometry/Thermo/FromBregman.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **13**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/FromBregman.lean` | `advisory` | 30 | 0 | 13 | 4 | 17 |

## Findings by file

### `lean/InfoGeometry/Thermo/FromBregman.lean`
- module: `InfoGeometry.Thermo.FromBregman`
- status: `advisory`
- debt_score: `30`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L61 [soft] `simp-law-injection` in `simp-declaration entropicTransportEnergyFromBregman_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration entropicTransportPlanFromBregman_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration bayesianFreeEnergyFromBregman_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L90 [advisory] `existential-packaging` in `lemma freeEnergyDivergence_def` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L90 [soft] `skeletal-proof` in `lemma freeEnergyDivergence_def` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `simp-law-injection` in `simp-declaration partitionDivergence_eq_Z` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `skeletal-proof` in `lemma partitionDivergence_pos` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `lemma gibbsProbFromBregman_nonneg` — proof appears to close via minimal tactic one-liner
  - L126 [advisory] `existential-packaging` in `lemma gibbsProbFromBregman_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L126 [soft] `skeletal-proof` in `lemma gibbsProbFromBregman_sum_one` — proof appears to close via minimal tactic one-liner
  - L134 [advisory] `existential-packaging` in `lemma gibbsProbFromBregman_eq_weight_over_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L134 [soft] `skeletal-proof` in `lemma gibbsProbFromBregman_eq_weight_over_partition` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `simp-law-injection` in `simp-declaration freeEnergyDivergence_eq_freeEnergyFromBregman` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L148 [soft] `skeletal-proof` in `lemma freeEnergyFromBregman_eq_internal_sub_scale_entropy` — proof appears to close via minimal tactic one-liner
  - L170 [soft] `skeletal-proof` in `lemma bayesianFreeEnergyFromBregman_eq_internal_sub_scale_entropy` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `lemma KL_param_eq_bregman_energy` — proof appears to close via minimal tactic one-liner

