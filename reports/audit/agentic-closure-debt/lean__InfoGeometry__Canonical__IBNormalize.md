# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.535863+00:00`
Root: `lean/InfoGeometry/Canonical/IBNormalize.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **3**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBNormalize.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBNormalize.lean`
- module: `InfoGeometry.Canonical.IBNormalize`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `existential-packaging` in `theorem probMeasureToPMF_normalize_discreteScoreMeasure` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L26 [soft] `skeletal-proof` in `theorem probMeasureToPMF_normalize_discreteScoreMeasure` — proof appears to close via minimal tactic one-liner
  - L43 [advisory] `local-hypothesis-injection` in `theorem probMeasureToPMF_normalize_discreteScoreMeasure` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [advisory] `existential-packaging` in `theorem baScoreFrozenMeasure_normalize_eq_stepFrozen` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L66 [soft] `skeletal-proof` in `theorem baScoreFrozenMeasure_normalize_eq_stepFrozen` — proof appears to close via minimal tactic one-liner
  - L86 [advisory] `existential-packaging` in `theorem baScoreMeasure_normalize_eq_step` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L86 [soft] `skeletal-proof` in `theorem baScoreMeasure_normalize_eq_step` — proof appears to close via minimal tactic one-liner

