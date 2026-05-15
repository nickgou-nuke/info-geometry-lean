# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.218026+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralDrazinLightConeBridge.lean`
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
| `lean/InfoGeometry/Canonical/ChiralDrazinLightConeBridge.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralDrazinLightConeBridge.lean`
- module: `InfoGeometry.Canonical.ChiralDrazinLightConeBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L69 [soft] `skeletal-proof` in `theorem minusProjector_eq_spectralComplementaryProjector_of_eps_eq_GammaS` — proof appears to close via minimal tactic one-liner
  - L139 [soft] `skeletal-proof` in `theorem chiralAnomaly_eq_uPlus_metricProjector_sub_uMinus_metricProjector` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `theorem rightChiralAnomaly_eq_uPlus_mpRangeProjector_sub_uMinus_mpRangeProjector` — proof appears to close via minimal tactic one-liner

