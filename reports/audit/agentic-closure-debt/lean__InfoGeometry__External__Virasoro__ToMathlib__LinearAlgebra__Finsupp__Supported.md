# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:33.470079+00:00`
Root: `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Finsupp/Supported.lean`
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
| `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Finsupp/Supported.lean` | `advisory` | 2 | 0 | 0 | 2 | 2 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/ToMathlib/LinearAlgebra/Finsupp/Supported.lean`
- module: `InfoGeometry.External.Virasoro.ToMathlib.LinearAlgebra.Finsupp.Supported`
- status: `advisory`
- debt_score: `2`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [advisory] `local-hypothesis-injection` in `lemma finsum_mem_mem_span` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

