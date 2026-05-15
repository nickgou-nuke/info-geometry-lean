# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:46.022186+00:00`
Root: `lean/InfoGeometry/KK/CompactOperatorBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **4**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/CompactOperatorBridge.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/KK/CompactOperatorBridge.lean`
- module: `InfoGeometry.KK.CompactOperatorBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [soft] `skeletal-proof` in `lemma isCompactEnd_zero` — proof appears to close via minimal tactic one-liner
  - L18 [soft] `skeletal-proof` in `lemma isCompactEnd_add` — proof appears to close via minimal tactic one-liner
  - L23 [soft] `skeletal-proof` in `lemma isCompactEnd_smul` — proof appears to close via minimal tactic one-liner
  - L28 [soft] `skeletal-proof` in `lemma isCompactEnd_of_finiteDimensional` — proof appears to close via minimal tactic one-liner
  - L43 [advisory] `local-hypothesis-injection` in `lemma isCompactEnd_of_finiteDimensional` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L45 [advisory] `local-hypothesis-injection` in `lemma isCompactEnd_of_finiteDimensional` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

