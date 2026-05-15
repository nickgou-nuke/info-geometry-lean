# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.202776+00:00`
Root: `lean/InfoGeometry/Canonical/CauchyResidueReadback.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CauchyResidueReadback.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/CauchyResidueReadback.lean`
- module: `InfoGeometry.Canonical.CauchyResidueReadback`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L36 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [soft] `skeletal-proof` in `theorem cauchy_vanishing_of_homologous_zero` — proof appears to close via minimal tactic one-liner
  - L75 [advisory] `local-hypothesis-injection` in `theorem cauchy_vanishing_of_homologous_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

