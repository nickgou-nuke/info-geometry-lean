# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:41.905223+00:00`
Root: `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **8**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean` | `advisory` | 17 | 0 | 8 | 1 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/PhaseSpaceGeneralizedMetricChiralityBridge.lean`
- module: `InfoGeometry.Canonical.PhaseSpaceGeneralizedMetricChiralityBridge`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `simp-law-injection` in `simp-declaration to_doubled_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration to_doubled_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration to_doubled_neg` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration to_doubled_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration fromDoubledCopyRho_toDoubledCopyRho` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration toDoubledCopyRho_fromDoubledCopyRho` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L335 [soft] `simp-law-injection` in `simp-declaration ofMetric_plusProjector_realized_is_chiralityPlus_fixed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L361 [soft] `simp-law-injection` in `simp-declaration ofMetric_minusProjector_realized_is_chiralityMinus_fixed` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

