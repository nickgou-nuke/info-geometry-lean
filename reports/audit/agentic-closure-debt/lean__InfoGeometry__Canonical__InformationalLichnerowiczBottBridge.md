# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:20.637129+00:00`
Root: `lean/InfoGeometry/Canonical/InformationalLichnerowiczBottBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **2**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/InformationalLichnerowiczBottBridge.lean` | `advisory` | 8 | 0 | 2 | 4 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/InformationalLichnerowiczBottBridge.lean`
- module: `InfoGeometry.Canonical.InformationalLichnerowiczBottBridge`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L35 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L65 [soft] `skeletal-proof` in `theorem spectralDirac_sq_eq_neg_id_of_operatorialTransport` — proof appears to close via minimal tactic one-liner
  - L92 [soft] `skeletal-proof` in `theorem lichnerowiczBalancedCl11_of_operatorialTransport` — proof appears to close via minimal tactic one-liner
  - L98 [advisory] `local-hypothesis-injection` in `theorem lichnerowiczBalancedCl11_of_operatorialTransport` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

