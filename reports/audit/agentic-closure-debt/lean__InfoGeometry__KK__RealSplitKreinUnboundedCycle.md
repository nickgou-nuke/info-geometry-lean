# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:47.714236+00:00`
Root: `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **9**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean` | `advisory` | 19 | 0 | 9 | 1 | 10 |

## Findings by file

### `lean/InfoGeometry/KK/RealSplitKreinUnboundedCycle.lean`
- module: `InfoGeometry.KK.RealSplitKreinUnboundedCycle`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.D` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L42 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.closed_graph` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.grade_preserves_domain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.regular` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.D_odd` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.D_krein_skewAdj` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.commutator` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field RealSplitKreinUnboundedCycle.commutator_formula` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `simp-law-injection` in `simp-declaration resolvent_mem_domain` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

