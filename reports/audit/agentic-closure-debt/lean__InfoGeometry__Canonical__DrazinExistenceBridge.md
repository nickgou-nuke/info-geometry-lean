# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:02.440544+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **1**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean` | `advisory` | 11 | 0 | 1 | 9 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinExistenceBridge.lean`
- module: `InfoGeometry.Canonical.DrazinExistenceBridge`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [advisory] `existential-packaging` in `theorem exists_canonicalDrazinInverse_global` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L58 [advisory] `existential-packaging` in `theorem exists_canonicalDrazinInverse_global_endCLM` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L58 [soft] `skeletal-proof` in `theorem exists_canonicalDrazinInverse_global_endCLM` — proof appears to close via minimal tactic one-liner
  - L72 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L74 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L76 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L84 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L90 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `local-hypothesis-injection` in `theorem exists_canonicalDrazinInverse_global_endCLM` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

