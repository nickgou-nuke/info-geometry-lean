# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:02.790684+00:00`
Root: `lean/InfoGeometry/Meta/CurvatureTelemetry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **3**
- Hard: **1**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=0, open_gap=1

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Meta/CurvatureTelemetry.lean` | `open_gap` | 8 | 1 | 1 | 1 | 3 |

## Findings by file

### `lean/InfoGeometry/Meta/CurvatureTelemetry.lean`
- module: `InfoGeometry.Meta.CurvatureTelemetry`
- status: `open_gap`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L22 [soft] `law-field-locker` in `structure-field CurvatureStats.exactSyntacticMatch` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

