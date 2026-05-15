# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.111807+00:00`
Root: `lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **8**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean` | `advisory` | 21 | 0 | 8 | 5 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularHamiltonianPregSupportBridge.lean`
- module: `InfoGeometry.Canonical.ModularHamiltonianPregSupportBridge`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L65 [soft] `skeletal-proof` in `theorem log_defined_on_Preg_of_regularSpectrumPositive` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `theorem K_neg_log_PregDelta_eq_Kreg` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem Kambient_eq_compress_Preg_K_neg_log_PregDelta` — proof appears to close via minimal tactic one-liner
  - L110 [soft] `skeletal-proof` in `theorem K_neg_log_PregDelta_support_package` — proof appears to close via minimal tactic one-liner
  - L120 [advisory] `local-hypothesis-injection` in `theorem K_neg_log_PregDelta_support_package` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [soft] `skeletal-proof` in `theorem Delta_reg_eq_compress_Preg_canonicalDelta` — proof appears to close via minimal tactic one-liner
  - L172 [soft] `skeletal-proof` in `theorem Kambient_eq_compress_Preg_neg_canonicalDeltaLog` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem canonicalTomita_support_package_on_Preg_of_certifiedReduction` — proof appears to close via minimal tactic one-liner
  - L198 [advisory] `local-hypothesis-injection` in `theorem canonicalTomita_support_package_on_Preg_of_certifiedReduction` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L224 [soft] `skeletal-proof` in `theorem Kphys_eq_metric_compress_of_canonicalTomita` — proof appears to close via minimal tactic one-liner

