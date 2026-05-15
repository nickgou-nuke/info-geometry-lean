# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:32.217958+00:00`
Root: `lean/InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **2**
- Hard: **0**
- Soft: **1**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean` | `advisory` | 3 | 0 | 1 | 1 | 2 |

## Findings by file

### `lean/InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean`
- module: `InfoGeometry.ProjectiveFoundation.RealProjectiveDescent`
- status: `advisory`
- debt_score: `3`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `law-field-locker` in `class-field CenterActsTrivially.center_smul_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

