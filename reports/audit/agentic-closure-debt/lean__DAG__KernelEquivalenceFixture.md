# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:23.040786+00:00`
Root: `lean/DAG/KernelEquivalenceFixture.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **0**
- Soft: **2**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/DAG/KernelEquivalenceFixture.lean` | `advisory` | 5 | 0 | 2 | 1 | 3 |

## Findings by file

### `lean/DAG/KernelEquivalenceFixture.lean`
- module: `DAG.KernelEquivalenceFixture`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L10 [soft] `skeletal-proof` in `theorem trueA` — proof appears to close via minimal tactic one-liner
  - L13 [soft] `skeletal-proof` in `theorem trueB` — proof appears to close via minimal tactic one-liner

