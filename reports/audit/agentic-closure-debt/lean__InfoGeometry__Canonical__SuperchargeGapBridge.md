# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.810701+00:00`
Root: `lean/InfoGeometry/Canonical/SuperchargeGapBridge.lean`
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
| `lean/InfoGeometry/Canonical/SuperchargeGapBridge.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperchargeGapBridge.lean`
- module: `InfoGeometry.Canonical.SuperchargeGapBridge`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L28 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L30 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [soft] `simp-law-injection` in `simp-declaration flatParityModularGap_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `skeletal-proof` in `theorem flatParityModularGap_eq_zero` — proof appears to close via minimal tactic one-liner
  - L58 [soft] `simp-law-injection` in `simp-declaration transportedParityModularGap_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem transportedParityModularGap_zero` — proof appears to close via minimal tactic one-liner
  - L65 [soft] `simp-law-injection` in `simp-declaration transportedParityModularGap_zero_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

