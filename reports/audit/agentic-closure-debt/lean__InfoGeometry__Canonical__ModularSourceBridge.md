# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:29.970716+00:00`
Root: `lean/InfoGeometry/Canonical/ModularSourceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **1**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ModularSourceBridge.lean` | `advisory` | 10 | 0 | 1 | 8 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/ModularSourceBridge.lean`
- module: `InfoGeometry.Canonical.ModularSourceBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L17 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L19 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L50 [soft] `skeletal-proof` in `theorem sourcedModularGenerator_bulk_invariant` — proof appears to close via minimal tactic one-liner
  - L62 [advisory] `local-hypothesis-injection` in `theorem sourcedModularGenerator_bulk_invariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [advisory] `local-hypothesis-injection` in `theorem sourcedModularGenerator_boundary_excitation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `local-hypothesis-injection` in `theorem sourcedModularGenerator_boundary_excitation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem sourcedModularGenerator_boundary_excitation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L101 [advisory] `local-hypothesis-injection` in `theorem sourcedModularGenerator_boundary_excitation` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

