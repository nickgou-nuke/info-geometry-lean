# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:38.224970+00:00`
Root: `lean/InfoGeometry/Canonical/OperatorialCramerRao.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **9**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/OperatorialCramerRao.lean` | `advisory` | 22 | 0 | 9 | 4 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/OperatorialCramerRao.lean`
- module: `InfoGeometry.Canonical.OperatorialCramerRao`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [soft] `simp-law-injection` in `simp-declaration comparisonStateGeneratorMetric_self_eq_norm_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_self_eq_norm_sq` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_self_nonneg` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_sq_le` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem comparisonStateGeneratorMetric_self_pos_of_apply_ne_zero` — proof appears to close via minimal tactic one-liner
  - L89 [advisory] `local-hypothesis-injection` in `theorem one_le_comparisonStateGeneratorMetric_self_mul_self_of_unit_response` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [advisory] `local-hypothesis-injection` in `theorem inv_comparisonStateGeneratorMetric_self_le_of_unit_response` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L120 [soft] `simp-law-injection` in `simp-declaration toRelationalInformationDatum_comparisonGeneratorMetric_self_eq_norm_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorMetric_self_eq_norm_sq` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_comparisonGeneratorMetric_sq_le` — proof appears to close via minimal tactic one-liner
  - L158 [soft] `skeletal-proof` in `theorem toRelationalInformationDatum_inv_comparisonGeneratorMetric_self_le_of_unit_response` — proof appears to close via minimal tactic one-liner

