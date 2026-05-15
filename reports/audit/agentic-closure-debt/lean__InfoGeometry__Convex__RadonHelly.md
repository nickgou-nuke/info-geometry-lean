# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.969020+00:00`
Root: `lean/InfoGeometry/Convex/RadonHelly.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **0**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/RadonHelly.lean` | `advisory` | 10 | 0 | 0 | 10 | 10 |

## Findings by file

### `lean/InfoGeometry/Convex/RadonHelly.lean`
- module: `InfoGeometry.Convex.RadonHelly`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L18 [advisory] `existential-packaging` in `theorem radon_partition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L27 [advisory] `existential-packaging` in `theorem helly_theorem'` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L34 [advisory] `existential-packaging` in `theorem helly_theorem` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L43 [advisory] `existential-packaging` in `theorem helly_theorem_set'` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L51 [advisory] `existential-packaging` in `theorem helly_theorem_set` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L65 [advisory] `existential-packaging` in `theorem helly_theorem_compact'` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L74 [advisory] `existential-packaging` in `theorem helly_theorem_compact` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L84 [advisory] `existential-packaging` in `theorem helly_theorem_set_compact'` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L94 [advisory] `existential-packaging` in `theorem helly_theorem_set_compact` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

