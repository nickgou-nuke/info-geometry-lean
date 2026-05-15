# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:42.528664+00:00`
Root: `lean/InfoGeometry/Canonical/BerryPhase.lean`
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
| `lean/InfoGeometry/Canonical/BerryPhase.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/BerryPhase.lean`
- module: `InfoGeometry.Canonical.BerryPhase`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L21 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [soft] `skeletal-proof` in `theorem hestenesWeylModularBerryPhaseReadout_eq_berryOf_hestenesWeylConnectionGenerator_add_relativeModularSourceDeriv_of_commute_gaugePart` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `theorem informationBerryPhase_eq_loopLength_mul_chiralAnomalyIndex` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `theorem informationBerryPhase_eq_loopLength_mul_epsilon_mul_rank` — proof appears to close via minimal tactic one-liner
  - L79 [soft] `skeletal-proof` in `theorem informationBerryPhase_ne_zero_of_loopLength_ne_zero_of_chiralAnomalyIndex_ne_zero` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `theorem berry_phase_vanishes_for_normal` — proof appears to close via minimal tactic one-liner

