# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:18.518677+00:00`
Root: `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **12**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean` | `advisory` | 25 | 0 | 12 | 1 | 13 |

## Findings by file

### `lean/InfoGeometry/Clifford/NeutralPhaseSpaceDoubledBridge.lean`
- module: `InfoGeometry.Clifford.NeutralPhaseSpaceDoubledBridge`
- status: `advisory`
- debt_score: `25`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L296 [soft] `simp-law-injection` in `simp-declaration phaseJEquiv_toLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L301 [soft] `simp-law-injection` in `simp-declaration phaseEpsilonEquiv_toLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L305 [soft] `simp-law-injection` in `simp-declaration phaseRotationEquiv_toLinearMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L339 [soft] `simp-law-injection` in `simp-declaration toDoubledCopyRho_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L346 [soft] `simp-law-injection` in `simp-declaration fromDoubledCopyRho_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L350 [soft] `simp-law-injection` in `simp-declaration realizeToDoubledRho_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L362 [soft] `simp-law-injection` in `simp-declaration phaseJ_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L367 [soft] `simp-law-injection` in `simp-declaration phaseEpsilon_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L372 [soft] `simp-law-injection` in `simp-declaration phaseRotation_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L381 [soft] `simp-law-injection` in `simp-declaration phasePlusProjector_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L387 [soft] `simp-law-injection` in `simp-declaration phaseMinusProjector_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L393 [soft] `simp-law-injection` in `simp-declaration modularRotation_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

