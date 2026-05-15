# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:03.179562+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinHodgeChiralBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **8**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinHodgeChiralBridge.lean` | `advisory` | 20 | 0 | 8 | 4 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinHodgeChiralBridge.lean`
- module: `InfoGeometry.Canonical.DrazinHodgeChiralBridge`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L66 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L66 [soft] `section-law-variable` in `variable B` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L97 [soft] `skeletal-proof` in `theorem hodgeStar_eq_GammaS` — proof appears to close via minimal tactic one-liner
  - L159 [soft] `skeletal-proof` in `theorem hodgeASD_eq_drazinDefect` — proof appears to close via minimal tactic one-liner
  - L312 [soft] `skeletal-proof` in `theorem hodgeDomainProjector_eq_mpLeftProjector` — proof appears to close via minimal tactic one-liner
  - L317 [soft] `skeletal-proof` in `theorem hodgeRangeProjector_eq_mpRightProjector` — proof appears to close via minimal tactic one-liner
  - L375 [soft] `skeletal-proof` in `theorem diracPlus_eq_splitCl11_uMinus` — proof appears to close via minimal tactic one-liner
  - L391 [soft] `skeletal-proof` in `theorem diracMinus_eq_splitCl11_uPlus` — proof appears to close via minimal tactic one-liner
  - L418 [soft] `skeletal-proof` in `theorem laplacian_commutes_GammaS` — proof appears to close via minimal tactic one-liner
  - L421 [advisory] `local-hypothesis-injection` in `theorem laplacian_commutes_GammaS` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

