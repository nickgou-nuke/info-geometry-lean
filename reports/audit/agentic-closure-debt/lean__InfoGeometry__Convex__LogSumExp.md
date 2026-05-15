# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.700146+00:00`
Root: `lean/InfoGeometry/Convex/LogSumExp.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **1**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/LogSumExp.lean` | `advisory` | 6 | 0 | 1 | 4 | 5 |

## Findings by file

### `lean/InfoGeometry/Convex/LogSumExp.lean`
- module: `InfoGeometry.Convex.LogSumExp`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `existential-packaging` in `lemma sumExp_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L68 [advisory] `local-hypothesis-injection` in `theorem lse_add_uniformShift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `theorem lse_add_uniformShift` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L71 [soft] `skeletal-proof` in `theorem softmax_add_uniformShift` — proof appears to close via minimal tactic one-liner

