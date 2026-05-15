# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:59.153212+00:00`
Root: `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **12**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean` | `advisory` | 28 | 0 | 12 | 4 | 16 |

## Findings by file

### `lean/InfoGeometry/Canonical/DensityWeightIntertwinerBridge.lean`
- module: `InfoGeometry.Canonical.DensityWeightIntertwinerBridge`
- status: `advisory`
- debt_score: `28`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L84 [soft] `simp-law-injection` in `simp-declaration projectiveDensityWeightHamiltonianProfile_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L118 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L120 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L131 [soft] `simp-law-injection` in `simp-declaration densityWeightPhaseAxis_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration densityWeightPhaseAxis_eq_modularComplexI` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `simp-law-injection` in `simp-declaration densityWeightPhaseAxis_eq_dilationOperator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L164 [soft] `simp-law-injection` in `simp-declaration densityWeightLiftedTransportGenerator_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [soft] `simp-law-injection` in `simp-declaration densityWeightLiftedModularSeed_eq_transportGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L187 [soft] `skeletal-proof` in `theorem densityWeightLiftedModularSeed_eq_transportGenerator` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `simp-law-injection` in `simp-declaration densityWeightLiftedDynamics_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L300 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L316 [soft] `simp-law-injection` in `simp-declaration densityWeightWeylIntertwiners_of_strictSymmetry_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L318 [soft] `skeletal-proof` in `theorem densityWeightWeylIntertwiners_of_strictSymmetry_fst` — proof appears to close via minimal tactic one-liner
  - L323 [soft] `simp-law-injection` in `simp-declaration densityWeightWeylIntertwiners_of_strictSymmetry_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L325 [soft] `skeletal-proof` in `theorem densityWeightWeylIntertwiners_of_strictSymmetry_snd` — proof appears to close via minimal tactic one-liner

