# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:41.181660+00:00`
Root: `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/AttentionPolarizedGibbsBridge.lean`
- module: `InfoGeometry.Canonical.AttentionPolarizedGibbsBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration polarizedPlusParams_energy` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L36 [soft] `skeletal-proof` in `theorem polarizedPlusParams_energy_eq_neg_dot_plus_half_norms` — proof appears to close via minimal tactic one-liner
  - L46 [advisory] `existential-packaging` in `theorem polarizedPlusAttentionWeights_eq_softmax_score` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L56 [soft] `simp-law-injection` in `simp-declaration partition_polarizedPlusParams_eq_logitSum` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [advisory] `existential-packaging` in `theorem gibbsWeight_polarizedPlusParams_eq_polarizedPlusAttentionWeights` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L115 [advisory] `existential-packaging` in `theorem polarizedPlusAttentionHead_eq_gibbsExpectation` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

