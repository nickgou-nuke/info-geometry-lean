# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:18.875614+00:00`
Root: `lean/DAG/BlockExport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **2**
- Soft: **0**
- Advisory: **1**
- File status counts: clean=0, advisory=0, open_gap=1

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/DAG/BlockExport.lean` | `open_gap` | 11 | 2 | 0 | 1 | 3 |

## Findings by file

### `lean/DAG/BlockExport.lean`
- module: `DAG.BlockExport`
- status: `open_gap`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L247 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking
  - L366 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

