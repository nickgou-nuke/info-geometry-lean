# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:06.895335+00:00`
Root: `lean/InfoGeometry/Canonical/TopologicalResidue.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/TopologicalResidue.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/TopologicalResidue.lean`
- module: `InfoGeometry.Canonical.TopologicalResidue`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L63 [soft] `skeletal-proof` in `theorem informationalZeroMode_iff_eq_zero` — proof appears to close via minimal tactic one-liner
  - L69 [advisory] `local-hypothesis-injection` in `theorem informationalZeroMode_iff_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L115 [soft] `skeletal-proof` in `theorem wittenIndexResidue_eq_analyticalIndex_modular_j` — proof appears to close via minimal tactic one-liner
  - L130 [soft] `skeletal-proof` in `theorem wittenIndexResidue_eq_zero` — proof appears to close via minimal tactic one-liner
  - L134 [advisory] `local-hypothesis-injection` in `theorem wittenIndexResidue_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [advisory] `local-hypothesis-injection` in `theorem wittenIndexResidue_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L140 [advisory] `local-hypothesis-injection` in `theorem wittenIndexResidue_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L142 [advisory] `local-hypothesis-injection` in `theorem wittenIndexResidue_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [soft] `skeletal-proof` in `theorem canonicalSuperchargeMultiplet_wittenIndexResidue_eq_zero` — proof appears to close via minimal tactic one-liner

