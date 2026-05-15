# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:27.391956+00:00`
Root: `lean/InfoGeometry/ErlangenLanglandsLane.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **4**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ErlangenLanglandsLane.lean` | `advisory` | 12 | 0 | 4 | 4 | 8 |

## Findings by file

### `lean/InfoGeometry/ErlangenLanglandsLane.lean`
- module: `InfoGeometry.ErlangenLanglandsLane`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L84 [soft] `law-field-locker` in `structure-field LanglandsGeometryArithmeticIntertwiner.bulkTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L86 [soft] `law-field-locker` in `structure-field LanglandsGeometryArithmeticIntertwiner.boundaryTransport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [soft] `law-field-locker` in `structure-field LanglandsGeometryArithmeticIntertwiner.siegel_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L93 [soft] `law-field-locker` in `structure-field LanglandsGeometryArithmeticIntertwiner.boundaryProjector_transport` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L123 [advisory] `existential-packaging` in `def LanglandsLaneCoreTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L168 [advisory] `existential-packaging` in `theorem constructLanglandsLanePacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L274 [advisory] `existential-packaging` in `theorem constructLanglandsLanePacket_withGeometry` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

