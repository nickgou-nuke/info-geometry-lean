# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:37.946595+00:00`
Root: `lean/InfoGeometry/Canonical/ActionDuality.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **0**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ActionDuality.lean` | `advisory` | 3 | 0 | 0 | 3 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/ActionDuality.lean`
- module: `InfoGeometry.Canonical.ActionDuality`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `existential-packaging` in `theorem einsteinHilbertAction_eq_neg_six_dual_pairing_sub_dual_of_compatible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L54 [advisory] `existential-packaging` in `theorem einsteinHilbertAction_and_zeroGap_of_compatible` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

