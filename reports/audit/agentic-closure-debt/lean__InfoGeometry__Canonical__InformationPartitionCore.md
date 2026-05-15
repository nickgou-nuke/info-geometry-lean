# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:20.182723+00:00`
Root: `lean/InfoGeometry/Canonical/InformationPartitionCore.lean`
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
| `lean/InfoGeometry/Canonical/InformationPartitionCore.lean` | `advisory` | 11 | 0 | 4 | 3 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/InformationPartitionCore.lean`
- module: `InfoGeometry.Canonical.InformationPartitionCore`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L43 [soft] `simp-law-injection` in `simp-declaration informationPartitionFunction_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration informationPartitionFunction_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `skeletal-proof` in `theorem hasDerivAt_informationPartitionFunction_zero` — proof appears to close via minimal tactic one-liner
  - L63 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_informationPartitionFunction_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `theorem hasDerivAt_logInformationPartitionFunction_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [soft] `skeletal-proof` in `theorem hasDerivAt_logInformationPartitionFunction_zero_of_normalized` — proof appears to close via minimal tactic one-liner

