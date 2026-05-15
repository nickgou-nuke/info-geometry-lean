# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:39.747471+00:00`
Root: `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **2**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean` | `advisory` | 7 | 0 | 2 | 3 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/AnomalyOwnerMap.lean`
- module: `InfoGeometry.Canonical.AnomalyOwnerMap`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `skeletal-proof` in `theorem drazin_dilation_anomaly_corridor` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem chiral_anomaly_is_skew_adjoint` — proof appears to close via minimal tactic one-liner
  - L60 [advisory] `bridge-shaped-declaration` in `theorem anomaly_owner_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L89 [advisory] `bridge-shaped-declaration` in `theorem projector_noncommutativity_closure_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

