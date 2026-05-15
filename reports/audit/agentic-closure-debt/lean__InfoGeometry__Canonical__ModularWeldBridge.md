# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:31.854168+00:00`
Root: `lean/InfoGeometry/Canonical/ModularWeldBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **17**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularWeldBridge.lean` | `advisory` | 35 | 0 | 17 | 1 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularWeldBridge.lean`
- module: `InfoGeometry.Canonical.ModularWeldBridge`
- status: `advisory`
- debt_score: `35`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L88 [soft] `skeletal-proof` in `theorem finiteDiagonalShadow_relativeModularOperator_eq_exp_relativeLogDensity` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `theorem FiniteDiagonalModularWeldBridge` — proof appears to close via minimal tactic one-liner
  - L104 [soft] `skeletal-proof` in `theorem finiteDiagonalModularWeldBridge_shadow_only` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem finiteDiagonalShadowLane` — proof appears to close via minimal tactic one-liner
  - L119 [soft] `skeletal-proof` in `theorem finiteDiagonalShadowLane_marker` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem finiteDiagonalShadowLane_projection_only` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `skeletal-proof` in `theorem finiteDiagonalShadowLane_only_projection` — proof appears to close via minimal tactic one-liner
  - L142 [soft] `simp-law-injection` in `simp-declaration relativeLogDensityOperator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L182 [soft] `skeletal-proof` in `theorem relativeModularOperator_eq_exp_relativeLogDensityOperator_self` — proof appears to close via minimal tactic one-liner
  - L187 [soft] `simp-law-injection` in `simp-declaration exp_relativeLogDensityOperator_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L196 [soft] `skeletal-proof` in `theorem finiteDiagonalShadow_exp_self_is_one` — proof appears to close via minimal tactic one-liner
  - L221 [soft] `skeletal-proof` in `theorem tomita_modularSign_flowUnitCocycle_isConnesCocycle` — proof appears to close via minimal tactic one-liner
  - L231 [soft] `simp-law-injection` in `simp-declaration tomita_modularSign_flow_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L234 [soft] `skeletal-proof` in `theorem tomita_modularSign_flow_one` — proof appears to close via minimal tactic one-liner
  - L247 [soft] `skeletal-proof` in `theorem tomita_modularSign_flowUnitCocycle_cocycle` — proof appears to close via minimal tactic one-liner
  - L259 [soft] `simp-law-injection` in `simp-declaration tomita_modularSign_flowUnitCocycle_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L265 [soft] `simp-law-injection` in `simp-declaration tomita_modularSign_flowUnitCocycle_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

