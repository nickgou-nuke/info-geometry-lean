# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:23.561103+00:00`
Root: `lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **2**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean` | `advisory` | 10 | 0 | 2 | 6 | 8 |

## Findings by file

### `lean/InfoGeometry/Core/CartanPhaseAxisForcing.lean`
- module: `InfoGeometry.Core.CartanPhaseAxisForcing`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [soft] `skeletal-proof` in `theorem commutator_KI_mem_odd` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `skeletal-proof` in `theorem eq_zero_of_mem_even_and_odd` — proof appears to close via minimal tactic one-liner
  - L61 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_mem_even_and_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_mem_even_and_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L63 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_mem_even_and_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_mem_even_and_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `theorem eq_zero_of_mem_even_and_odd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

