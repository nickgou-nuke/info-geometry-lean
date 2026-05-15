# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:41.461992+00:00`
Root: `lean/InfoGeometry/GrandUnification/ProjectiveCharacterGWBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/GrandUnification/ProjectiveCharacterGWBridge.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/GrandUnification/ProjectiveCharacterGWBridge.lean`
- module: `InfoGeometry.GrandUnification.ProjectiveCharacterGWBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L70 [soft] `skeletal-proof` in `theorem projectiveCharacter_partitionReadout_is_traceReadout` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem projectiveCharacter_logPartition_is_log_trace` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem projectiveCharacter_kl_eq_expectation_logDensity` — proof appears to close via minimal tactic one-liner
  - L102 [soft] `skeletal-proof` in `theorem projectiveCharacter_finiteSpectral_partitionNormalization` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `skeletal-proof` in `theorem finite_projective_shadow_only_ofModularReadout` — proof appears to close via minimal tactic one-liner

