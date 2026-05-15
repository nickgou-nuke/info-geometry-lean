# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:50.636357+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **2**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean` | `advisory` | 9 | 0 | 2 | 5 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralCliffordBridge.lean`
- module: `InfoGeometry.Canonical.ChiralCliffordBridge`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L64 [soft] `skeletal-proof` in `theorem anomaly_as_structure_constant` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem cartan_collapse_of_normal` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `local-hypothesis-injection` in `theorem cartan_collapse_of_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `theorem cartan_collapse_of_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `theorem cartan_collapse_of_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L89 [advisory] `local-hypothesis-injection` in `theorem cartan_collapse_of_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

