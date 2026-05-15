# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.451488+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **5**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean` | `advisory` | 11 | 0 | 5 | 1 | 6 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
- module: `InfoGeometry.KK.RealSplitKreinKasparovCycle`
- status: `advisory`
- debt_score: `11`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field RealSplitKreinKasparovCycle.F_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field RealSplitKreinKasparovCycle.F_skewAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field RealSplitKreinKasparovCycle.comm_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field RealSplitKreinKasparovCycle.superComm_eps_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field RealSplitKreinKasparovCycle.superComm_J_compact` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

