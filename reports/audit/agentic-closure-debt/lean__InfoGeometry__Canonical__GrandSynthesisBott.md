# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:12.076286+00:00`
Root: `lean/InfoGeometry/Canonical/GrandSynthesisBott.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **0**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/GrandSynthesisBott.lean` | `advisory` | 3 | 0 | 0 | 3 | 3 |

## Findings by file

### `lean/InfoGeometry/Canonical/GrandSynthesisBott.lean`
- module: `InfoGeometry.Canonical.GrandSynthesisBott`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L96 [advisory] `local-hypothesis-injection` in `theorem cl11BottLaplacian_eq_metricOp_form` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L99 [advisory] `local-hypothesis-injection` in `theorem cl11BottLaplacian_eq_metricOp_form` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

