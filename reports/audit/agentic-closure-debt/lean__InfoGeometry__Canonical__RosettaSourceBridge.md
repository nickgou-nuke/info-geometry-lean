# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:54.122674+00:00`
Root: `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **5**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/RosettaSourceBridge.lean`
- module: `InfoGeometry.Canonical.RosettaSourceBridge`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L39 [soft] `simp-law-injection` in `simp-declaration modularComplexI_toLinearMap_eq_realMajoranaKAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration complex_i_toLinearMap_eq_realMajoranaKAxis` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `skeletal-proof` in `theorem sourceTension_eq_transportedEinsteinResidual` — proof appears to close via minimal tactic one-liner
  - L76 [soft] `simp-law-injection` in `simp-declaration transportedEinsteinResidual_eq_einsteinInducedChemicalPotential` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration einsteinInducedChemicalPotential_lift_eq_einsteinFockDeformationOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

