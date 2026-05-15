# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:51.329332+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean`
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
| `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean` | `advisory` | 11 | 0 | 3 | 5 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralEinsteinBridge.lean`
- module: `InfoGeometry.Canonical.ChiralEinsteinBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [soft] `simp-law-injection` in `simp-declaration anomalyStressEnergyAt_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `simp-law-injection` in `simp-declaration anomalyStressEnergyAt_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [advisory] `existential-packaging` in `theorem einsteinEquation_of_anomaly_source` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L63 [advisory] `existential-packaging` in `theorem exists_einsteinEquation_of_bistochastic_routingAnomaly` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [soft] `skeletal-proof` in `theorem anomalyDriven_fixedpoint_tracks_source` — proof appears to close via minimal tactic one-liner
  - L119 [advisory] `local-hypothesis-injection` in `theorem anomalyDriven_fixedpoint_tracks_source` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [advisory] `local-hypothesis-injection` in `theorem anomalyDriven_fixedpoint_tracks_source` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

