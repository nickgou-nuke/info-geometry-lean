# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:43.594598+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovOptimalTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **5**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovOptimalTransport.lean` | `advisory` | 14 | 0 | 5 | 4 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovOptimalTransport.lean`
- module: `InfoGeometry.Canonical.BogoliubovOptimalTransport`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `skeletal-proof` in `theorem alignmentObstruction_eq_zero` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `skeletal-proof` in `theorem chiObstruction_eq_zero_iff_alignment` — proof appears to close via minimal tactic one-liner
  - L81 [soft] `skeletal-proof` in `theorem chiObstruction_ne_zero_iff_non_alignment` — proof appears to close via minimal tactic one-liner
  - L124 [soft] `skeletal-proof` in `theorem canonicalBogoliubovFlow_isOptimal` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem no_defect_leakage_of_optimal_flow` — proof appears to close via minimal tactic one-liner
  - L150 [advisory] `local-hypothesis-injection` in `theorem no_defect_leakage_of_optimal_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `local-hypothesis-injection` in `theorem no_defect_leakage_of_optimal_flow` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

