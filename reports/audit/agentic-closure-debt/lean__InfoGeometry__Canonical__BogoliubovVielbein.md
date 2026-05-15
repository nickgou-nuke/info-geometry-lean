# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.300591+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovVielbein.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovVielbein.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovVielbein.lean`
- module: `InfoGeometry.Canonical.BogoliubovVielbein`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L73 [soft] `skeletal-proof` in `lemma transportCommutator_expTransport` — proof appears to close via minimal tactic one-liner
  - L183 [soft] `skeletal-proof` in `theorem deriv_localFrame_at_zero` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem deriv_localFrame_at` — proof appears to close via minimal tactic one-liner

