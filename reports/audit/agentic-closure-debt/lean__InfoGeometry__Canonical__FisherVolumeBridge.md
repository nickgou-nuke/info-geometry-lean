# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:08.510643+00:00`
Root: `lean/InfoGeometry/Canonical/FisherVolumeBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **2**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/FisherVolumeBridge.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/FisherVolumeBridge.lean`
- module: `InfoGeometry.Canonical.FisherVolumeBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `skeletal-proof` in `theorem action_hessian_eq_fisher` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem operatorial_uncertainty_area_law` — proof appears to close via minimal tactic one-liner
  - L73 [advisory] `bridge-shaped-declaration` in `theorem metric_to_phase_readout_bridge` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L89 [advisory] `bridge-shaped-declaration` in `theorem metric_to_phase_readout_bridge_comp_complex_i` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

