# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.852433+00:00`
Root: `lean/InfoGeometry/Canonical/ModularOrientationContract.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularOrientationContract.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularOrientationContract.lean`
- module: `InfoGeometry.Canonical.ModularOrientationContract`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L47 [soft] `skeletal-proof` in `theorem canonical_seed_phaseAxis_eq_phaseAxisK` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem phaseAxis_flip_sq_eq_neg_id` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem commutantAction_invariant_under_modular_j_flip` — proof appears to close via minimal tactic one-liner
  - L129 [soft] `skeletal-proof` in `theorem orientationFlip_swaps_vacuum_polarizations_plus` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `skeletal-proof` in `theorem orientationFlip_swaps_vacuum_polarizations_minus` — proof appears to close via minimal tactic one-liner

