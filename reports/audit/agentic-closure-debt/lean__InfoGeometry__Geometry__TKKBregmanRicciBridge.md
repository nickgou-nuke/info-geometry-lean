# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:40.113004+00:00`
Root: `lean/InfoGeometry/Geometry/TKKBregmanRicciBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **4**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/TKKBregmanRicciBridge.lean` | `advisory` | 10 | 0 | 4 | 2 | 6 |

## Findings by file

### `lean/InfoGeometry/Geometry/TKKBregmanRicciBridge.lean`
- module: `InfoGeometry.Geometry.TKKBregmanRicciBridge`
- status: `advisory`
- debt_score: `10`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L67 [soft] `law-field-locker` in `structure-field TKKBregmanRicciBridge.stateOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field TKKBregmanRicciBridge.generatorOf` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field TKKBregmanRicciBridge.fluxScalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field TKKBregmanRicciBridge.scalar_ricciFlux_eq_bregman_secondVariation` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L178 [advisory] `existential-packaging` in `def TKKBregmanRicciBridgeOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

