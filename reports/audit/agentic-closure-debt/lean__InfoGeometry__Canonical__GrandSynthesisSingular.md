# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:12.330278+00:00`
Root: `lean/InfoGeometry/Canonical/GrandSynthesisSingular.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **0**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandSynthesisSingular.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandSynthesisSingular.lean`
- module: `InfoGeometry.Canonical.GrandSynthesisSingular`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L94 [advisory] `local-hypothesis-injection` in `theorem regularRadialTransportCloses_of_boundaryGenerator_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

