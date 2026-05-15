# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.498169+00:00`
Root: `lean/InfoGeometry/Canonical/IBFrozenDescent.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **4**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFrozenDescent.lean` | `advisory` | 16 | 0 | 4 | 8 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFrozenDescent.lean`
- module: `InfoGeometry.Canonical.IBFrozenDescent`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L105 [soft] `skeletal-proof` in `theorem ibBlahutArimotoStepFrozen_eq_frozenGibbs` — proof appears to close via minimal tactic one-liner
  - L124 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStepFrozen_eq_frozenGibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L233 [advisory] `local-hypothesis-injection` in `theorem ibFrozenFreeEnergy_eq_gap_minus_logPartition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L375 [soft] `skeletal-proof` in `theorem ibFrozenFreeEnergy_frozen_descent_internal` — proof appears to close via minimal tactic one-liner
  - L463 [soft] `skeletal-proof` in `theorem ibVariationalFunctional_frozen_descent` — proof appears to close via minimal tactic one-liner
  - L496 [soft] `skeletal-proof` in `theorem ibVariationalFunctionalLoose_eq_sum_local` — proof appears to close via minimal tactic one-liner
  - L549 [advisory] `local-hypothesis-injection` in `theorem ibVariationalFunctional_le_loose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L559 [advisory] `local-hypothesis-injection` in `theorem ibVariationalFunctional_le_loose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L566 [advisory] `local-hypothesis-injection` in `theorem ibVariationalFunctional_le_loose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L569 [advisory] `local-hypothesis-injection` in `theorem ibVariationalFunctional_le_loose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L763 [advisory] `local-hypothesis-injection` in `theorem ibBlahutArimotoStep_descent_frozenTarget` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

