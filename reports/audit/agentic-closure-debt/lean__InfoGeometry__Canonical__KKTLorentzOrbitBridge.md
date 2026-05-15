# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:22.394244+00:00`
Root: `lean/InfoGeometry/Canonical/KKTLorentzOrbitBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KKTLorentzOrbitBridge.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/KKTLorentzOrbitBridge.lean`
- module: `InfoGeometry.Canonical.KKTLorentzOrbitBridge`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L27 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L36 [soft] `skeletal-proof` in `theorem eps_mul_gOnePart` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem gOnePart_mul_eps` — proof appears to close via minimal tactic one-liner
  - L61 [soft] `skeletal-proof` in `theorem eps_mul_gNegOnePart` — proof appears to close via minimal tactic one-liner
  - L74 [soft] `skeletal-proof` in `theorem gNegOnePart_mul_eps` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `skeletal-proof` in `theorem eps_mul_gZeroPart_eq_gZeroPart_mul_eps` — proof appears to close via minimal tactic one-liner
  - L117 [soft] `skeletal-proof` in `theorem channelBoost_mul_gZeroPart_eq_gZeroPart_mul_channelBoost` — proof appears to close via minimal tactic one-liner
  - L146 [soft] `skeletal-proof` in `theorem channelBoost_mul_uPlus` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `skeletal-proof` in `theorem channelBoost_mul_uMinus` — proof appears to close via minimal tactic one-liner

