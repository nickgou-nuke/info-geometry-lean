# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.565828+00:00`
Root: `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **3**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean` | `advisory` | 12 | 0 | 3 | 6 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/BogoliubovWeightedKMSCertification.lean`
- module: `InfoGeometry.Canonical.BogoliubovWeightedKMSCertification`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L34 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L35 [soft] `skeletal-proof` in `theorem kLinear_iff_isPhaseLinear` — proof appears to close via minimal tactic one-liner
  - L49 [soft] `skeletal-proof` in `theorem kAntilinear_iff_isPhaseAntilinear` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `skeletal-proof` in `theorem kSplit_reconstruction_eq_phaseSplit` — proof appears to close via minimal tactic one-liner
  - L110 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L112 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L169 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

