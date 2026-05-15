# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:28.931890+00:00`
Root: `lean/InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **11**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean` | `advisory` | 23 | 0 | 11 | 1 | 12 |

## Findings by file

### `lean/InfoGeometry/Algebraic/NarainSupervolumeBridgeData.lean`
- module: `InfoGeometry.Algebraic.NarainSupervolumeBridgeData`
- status: `advisory`
- debt_score: `23`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.charge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.realifiedCharge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L46 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.realifiedCharge_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.parity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.supervolume_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.latticeSumReadout_eq_supervolumeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L67 [soft] `law-field-locker` in `structure-field NarainSupervolumeBridgeData.effectiveAction_eq_negLog_supervolumeReadout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L90 [soft] `simp-law-injection` in `simp-declaration latticeSum_eq_supervolume` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L92 [soft] `skeletal-proof` in `theorem latticeSum_eq_supervolume` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `simp-law-injection` in `simp-declaration effectiveAction_eq_negLog` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `skeletal-proof` in `theorem effectiveAction_eq_negLog` — proof appears to close via minimal tactic one-liner

