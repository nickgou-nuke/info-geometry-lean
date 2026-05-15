# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:30.144302+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/KLBregman.lean`
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
| `lean/InfoGeometry/ExponentialFamily/KLBregman.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/KLBregman.lean`
- module: `InfoGeometry.ExponentialFamily.KLBregman`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L45 [soft] `simp-law-injection` in `simp-declaration entropicTransportObjective_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration entropicTransportPotentialGap_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [advisory] `local-hypothesis-injection` in `lemma log_density_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `skeletal-proof` in `lemma entropicTransportObjective_eq_potentialGap_if_deriv_mean` — proof appears to close via minimal tactic one-liner

