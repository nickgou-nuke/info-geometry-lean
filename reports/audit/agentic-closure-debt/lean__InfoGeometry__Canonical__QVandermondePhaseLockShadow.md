# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:46.217472+00:00`
Root: `lean/InfoGeometry/Canonical/QVandermondePhaseLockShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **0**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/QVandermondePhaseLockShadow.lean` | `advisory` | 6 | 0 | 0 | 6 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/QVandermondePhaseLockShadow.lean`
- module: `InfoGeometry.Canonical.QVandermondePhaseLockShadow`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L71 [advisory] `local-hypothesis-injection` in `theorem norm_eq_of_unitPhase_of_collision` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L76 [advisory] `bridge-shaped-declaration` in `theorem two_node_phase_lock_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L94 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L154 [advisory] `bridge-shaped-declaration` in `theorem a2_phase_lock_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

