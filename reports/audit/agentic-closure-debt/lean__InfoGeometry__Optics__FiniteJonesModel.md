# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:27.547632+00:00`
Root: `lean/InfoGeometry/Optics/FiniteJonesModel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Optics/FiniteJonesModel.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Optics/FiniteJonesModel.lean`
- module: `InfoGeometry.Optics.FiniteJonesModel`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L49 [soft] `simp-law-injection` in `simp-declaration diagJones_00` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem diagJones_00` — proof appears to close via minimal tactic one-liner
  - L56 [soft] `simp-law-injection` in `simp-declaration diagJones_11` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `skeletal-proof` in `theorem diagJones_11` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `simp-law-injection` in `simp-declaration diagJones_01` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `theorem diagJones_01` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `simp-law-injection` in `simp-declaration diagJones_10` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `skeletal-proof` in `theorem diagJones_10` — proof appears to close via minimal tactic one-liner
  - L116 [soft] `skeletal-proof` in `theorem det2_diagJones` — proof appears to close via minimal tactic one-liner
  - L124 [soft] `skeletal-proof` in `theorem det2_brewsterMatrix` — proof appears to close via minimal tactic one-liner

