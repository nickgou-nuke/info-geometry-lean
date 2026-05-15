# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:05.736801+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinWitnessElimination.lean`
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
| `lean/InfoGeometry/Canonical/DrazinWitnessElimination.lean` | `advisory` | 12 | 0 | 5 | 2 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinWitnessElimination.lean`
- module: `InfoGeometry.Canonical.DrazinWitnessElimination`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L15 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L25 [soft] `skeletal-proof` in `theorem isDrazinInverse_drazinInverse` — proof appears to close via minimal tactic one-liner
  - L42 [soft] `simp-law-injection` in `simp-declaration drazinProjector_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration drazinComplementaryProjector_idempotent` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `simp-law-injection` in `simp-declaration drazinProjector_mul_drazinComplementaryProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [soft] `simp-law-injection` in `simp-declaration drazinComplementaryProjector_mul_drazinProjector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

