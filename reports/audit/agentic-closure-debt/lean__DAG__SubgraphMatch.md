# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:25.296310+00:00`
Root: `lean/DAG/SubgraphMatch.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **1**
- Soft: **0**
- Advisory: **1**
- File status counts: clean=0, advisory=0, open_gap=1

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/DAG/SubgraphMatch.lean` | `open_gap` | 6 | 1 | 0 | 1 | 2 |

## Findings by file

### `lean/DAG/SubgraphMatch.lean`
- module: `DAG.SubgraphMatch`
- status: `open_gap`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L103 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

