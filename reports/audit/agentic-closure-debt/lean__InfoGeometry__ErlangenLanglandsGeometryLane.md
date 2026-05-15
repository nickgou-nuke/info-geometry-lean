# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:27.133118+00:00`
Root: `lean/InfoGeometry/ErlangenLanglandsGeometryLane.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **4**
- Hard: **0**
- Soft: **2**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ErlangenLanglandsGeometryLane.lean` | `advisory` | 6 | 0 | 2 | 2 | 4 |

## Findings by file

### `lean/InfoGeometry/ErlangenLanglandsGeometryLane.lean`
- module: `InfoGeometry.ErlangenLanglandsGeometryLane`
- status: `advisory`
- debt_score: `6`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `law-field-locker` in `structure-field LanglandsLaneGeometryPacket.upperHalfPlane_is_Z` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field LanglandsLaneFullPacket.completed_compat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [advisory] `existential-packaging` in `def LanglandsLaneFullTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

