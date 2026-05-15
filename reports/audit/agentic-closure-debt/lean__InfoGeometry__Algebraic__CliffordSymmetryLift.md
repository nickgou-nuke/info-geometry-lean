# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:27.934326+00:00`
Root: `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean`
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
| `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean` | `advisory` | 9 | 0 | 4 | 1 | 5 |

## Findings by file

### `lean/InfoGeometry/Algebraic/CliffordSymmetryLift.lean`
- module: `InfoGeometry.Algebraic.CliffordSymmetryLift`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `simp-law-injection` in `simp-declaration toLinearEquiv_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `skeletal-proof` in `theorem toLinearEquiv_apply` — proof appears to close via minimal tactic one-liner
  - L50 [soft] `simp-law-injection` in `simp-declaration splitCliffordLift_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `skeletal-proof` in `theorem splitCliffordLift_apply` — proof appears to close via minimal tactic one-liner

