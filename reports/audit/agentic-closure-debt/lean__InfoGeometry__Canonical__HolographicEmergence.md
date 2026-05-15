# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:15.415254+00:00`
Root: `lean/InfoGeometry/Canonical/HolographicEmergence.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **0**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HolographicEmergence.lean` | `advisory` | 4 | 0 | 0 | 4 | 4 |

## Findings by file

### `lean/InfoGeometry/Canonical/HolographicEmergence.lean`
- module: `InfoGeometry.Canonical.HolographicEmergence`
- status: `advisory`
- debt_score: `4`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L72 [advisory] `bridge-shaped-declaration` in `theorem exists_gaugeOrderHysteresis_witness` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L72 [advisory] `existential-packaging` in `theorem exists_gaugeOrderHysteresis_witness` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

