# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:59.703456+00:00`
Root: `lean/InfoGeometry/MaxEnt/DualBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **3**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/MaxEnt/DualBridge.lean` | `advisory` | 16 | 0 | 3 | 10 | 13 |

## Findings by file

### `lean/InfoGeometry/MaxEnt/DualBridge.lean`
- module: `InfoGeometry.MaxEnt.DualBridge`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [advisory] `existential-packaging` in `def momentResidual` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L37 [soft] `simp-law-injection` in `simp-declaration momentResidual_eq_zero_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `skeletal-proof` in `lemma crossEntropyToGibbs_eq_dualObjective` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `lemma entropy_gibbs_eq_dualObjective` — proof appears to close via minimal tactic one-liner
  - L92 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L108 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L109 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L110 [advisory] `local-hypothesis-injection` in `theorem entropy_le_dualObjective_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `local-hypothesis-injection` in `theorem gibbs_maximizes_entropy_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [advisory] `local-hypothesis-injection` in `theorem gibbs_maximizes_entropy_on_constraint` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

