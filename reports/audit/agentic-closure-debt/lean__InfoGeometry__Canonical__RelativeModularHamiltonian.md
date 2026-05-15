# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:50.852948+00:00`
Root: `lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean`
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
| `lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/RelativeModularHamiltonian.lean`
- module: `InfoGeometry.Canonical.RelativeModularHamiltonian`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [advisory] `existential-packaging` in `def modularHamiltonianFromDiagonal` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L45 [soft] `simp-law-injection` in `simp-declaration modularHamiltonianFromDiagonal_diag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L51 [soft] `simp-law-injection` in `simp-declaration modularHamiltonianFromDiagonal_offdiag` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L142 [soft] `simp-law-injection` in `simp-declaration relativeModularHamiltonianExpectation_self` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

