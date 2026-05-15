# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:50.072489+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralAction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **7**
- Hard: **0**
- Soft: **1**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralAction.lean` | `advisory` | 8 | 0 | 1 | 6 | 7 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralAction.lean`
- module: `InfoGeometry.Canonical.ChiralAction`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [soft] `skeletal-proof` in `theorem chiral_action_reduces_for_normal` — proof appears to close via minimal tactic one-liner
  - L40 [advisory] `local-hypothesis-injection` in `theorem chiral_action_reduces_for_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L42 [advisory] `local-hypothesis-injection` in `theorem chiral_action_reduces_for_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L44 [advisory] `local-hypothesis-injection` in `theorem chiral_action_reduces_for_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L46 [advisory] `local-hypothesis-injection` in `theorem chiral_action_reduces_for_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L47 [advisory] `local-hypothesis-injection` in `theorem chiral_action_reduces_for_normal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

