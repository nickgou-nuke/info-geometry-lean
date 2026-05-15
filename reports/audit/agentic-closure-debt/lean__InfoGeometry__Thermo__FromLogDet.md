# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:46.895089+00:00`
Root: `lean/InfoGeometry/Thermo/FromLogDet.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **6**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Thermo/FromLogDet.lean` | `advisory` | 15 | 0 | 6 | 3 | 9 |

## Findings by file

### `lean/InfoGeometry/Thermo/FromLogDet.lean`
- module: `InfoGeometry.Thermo.FromLogDet`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `existential-packaging` in `def partitionFromLogDet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L49 [soft] `skeletal-proof` in `lemma partitionFromLogDet_pos'` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `skeletal-proof` in `lemma gibbsProbFromLogDet_nonneg` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `skeletal-proof` in `lemma partitionFromLogDet_ne_zero` — proof appears to close via minimal tactic one-liner
  - L66 [advisory] `existential-packaging` in `lemma gibbsProbFromLogDet_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [soft] `skeletal-proof` in `lemma gibbsProbFromLogDet_sum_one` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `simp-law-injection` in `simp-declaration freeEnergyFromLogDet_eq_neg_scale_log_partition` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `skeletal-proof` in `lemma freeEnergyFromLogDet_eq_internal_sub_scale_entropy` — proof appears to close via minimal tactic one-liner

