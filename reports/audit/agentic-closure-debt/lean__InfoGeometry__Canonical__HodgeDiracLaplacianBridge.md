# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:15.144058+00:00`
Root: `lean/InfoGeometry/Canonical/HodgeDiracLaplacianBridge.lean`
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
| `lean/InfoGeometry/Canonical/HodgeDiracLaplacianBridge.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/HodgeDiracLaplacianBridge.lean`
- module: `InfoGeometry.Canonical.HodgeDiracLaplacianBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L101 [soft] `skeletal-proof` in `theorem dirac_sq_commutes_hodge` — proof appears to close via minimal tactic one-liner
  - L132 [soft] `vacuous-prop` in `prop <vacuous>` — Prop declaration appears to reduce to True/False
  - L155 [advisory] `bridge-shaped-declaration` in `theorem centralReadout_is_witness_gated` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L155 [soft] `skeletal-proof` in `theorem centralReadout_is_witness_gated` — proof appears to close via minimal tactic one-liner

