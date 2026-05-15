# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:50.966022+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **4**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularHamiltonianSupport.lean`
- module: `InfoGeometry.Canonical.RelativeModularHamiltonianSupport`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L46 [soft] `simp-law-injection` in `simp-declaration supportRestrictedModularHamiltonianOperator_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `simp-law-injection` in `simp-declaration supportRestrictedModularHamiltonianOperator_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration supportRestrictedModularHamiltonianOperator_univ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration supportRestrictedModularHamiltonianOperator_empty` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

