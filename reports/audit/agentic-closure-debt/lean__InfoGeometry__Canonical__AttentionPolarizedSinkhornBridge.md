# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:41.297177+00:00`
Root: `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/AttentionPolarizedSinkhornBridge.lean`
- module: `InfoGeometry.Canonical.AttentionPolarizedSinkhornBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `simp-law-injection` in `simp-declaration polarizedPlusAttentionMatrix_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration polarizedPlusAttentionMatrix_apply_eq_gibbsWeight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `skeletal-proof` in `theorem polarizedPlusAttentionMatrix_row_sum_one` — proof appears to close via minimal tactic one-liner
  - L93 [advisory] `existential-packaging` in `theorem exists_perm_decomposition_of_bistochastic_polarizedPlusAttention` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

