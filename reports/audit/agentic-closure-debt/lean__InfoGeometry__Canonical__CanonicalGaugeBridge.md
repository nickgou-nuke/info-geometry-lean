# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.681699+00:00`
Root: `lean/InfoGeometry/Canonical/CanonicalGaugeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **9**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CanonicalGaugeBridge.lean` | `advisory` | 21 | 0 | 9 | 3 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/CanonicalGaugeBridge.lean`
- module: `InfoGeometry.Canonical.CanonicalGaugeBridge`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L29 [soft] `simp-law-injection` in `simp-declaration twoStateGap_self_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L50 [soft] `simp-law-injection` in `simp-declaration functionalShift_self_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L72 [soft] `simp-law-injection` in `simp-declaration comparisonTransportGenerator_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `simp-law-injection` in `simp-declaration comparisonInducedDynamics_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `simp-law-injection` in `simp-declaration firstVariation_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `simp-law-injection` in `simp-declaration comparisonGeneratorMetric_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `simp-law-injection` in `simp-declaration comparisonGeneratorPhase_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L140 [soft] `simp-law-injection` in `simp-declaration comparisonMetricReadout_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration comparisonPhaseReadout_referenceInvariant` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

