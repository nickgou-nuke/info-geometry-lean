# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:18.265539+00:00`
Root: `lean/InfoGeometry/Canonical/IBMeasure.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **6**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBMeasure.lean` | `advisory` | 19 | 0 | 6 | 7 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBMeasure.lean`
- module: `InfoGeometry.Canonical.IBMeasure`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [advisory] `existential-packaging` in `lemma partitionFunction_eq_lintegral` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [soft] `skeletal-proof` in `lemma partitionFunction_eq_lintegral` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `lemma IBPartitionFunction_eq_lintegral` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `theorem rnDeriv_IBUnnormalized_eq` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem IBNormalize_toMeasure_eq_inv_mass_smul_of_nonzero` — proof appears to close via minimal tactic one-liner
  - L115 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L123 [soft] `skeletal-proof` in `theorem IBGibbs_eq_unnormalized_smul_partition` — proof appears to close via minimal tactic one-liner
  - L132 [advisory] `local-hypothesis-injection` in `theorem IBGibbs_eq_unnormalized_smul_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L135 [advisory] `local-hypothesis-injection` in `theorem IBGibbs_eq_unnormalized_smul_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [advisory] `local-hypothesis-injection` in `theorem IBGibbs_eq_unnormalized_smul_partition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [soft] `skeletal-proof` in `theorem rnDeriv_IBGibbs_eq` — proof appears to close via minimal tactic one-liner
  - L168 [advisory] `local-hypothesis-injection` in `theorem rnDeriv_IBGibbs_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

