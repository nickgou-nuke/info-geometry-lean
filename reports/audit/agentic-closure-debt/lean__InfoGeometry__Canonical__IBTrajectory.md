# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:19.258798+00:00`
Root: `lean/InfoGeometry/Canonical/IBTrajectory.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **4**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBTrajectory.lean` | `advisory` | 13 | 0 | 4 | 5 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBTrajectory.lean`
- module: `InfoGeometry.Canonical.IBTrajectory`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L38 [soft] `simp-law-injection` in `simp-declaration ibTrajectory_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `simp-law-injection` in `simp-declaration ibTrajectory_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration ibTrajectory_eq_iterate` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [advisory] `existential-packaging` in `theorem exists_ibTrajectory` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L97 [advisory] `existential-packaging` in `theorem tendsto_ibTrajectory_fixedPoint` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L146 [advisory] `existential-packaging` in `theorem tendsto_ibTrajectory_fixedPoint_of_contracting` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L171 [advisory] `existential-packaging` in `theorem tendsto_ibTrajectory_fixedPoint_of_lipschitz` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L171 [soft] `skeletal-proof` in `theorem tendsto_ibTrajectory_fixedPoint_of_lipschitz` — proof appears to close via minimal tactic one-liner

