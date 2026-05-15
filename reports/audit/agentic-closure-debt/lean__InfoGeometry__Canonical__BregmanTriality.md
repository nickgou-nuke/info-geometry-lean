# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:46.328341+00:00`
Root: `lean/InfoGeometry/Canonical/BregmanTriality.lean`
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
| `lean/InfoGeometry/Canonical/BregmanTriality.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/Canonical/BregmanTriality.lean`
- module: `InfoGeometry.Canonical.BregmanTriality`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L12 [advisory] `existential-packaging` in `def softmaxBregmanAttention` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

