# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:44.956420+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectiveFoundation.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **11**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectiveFoundation.lean` | `advisory` | 24 | 0 | 11 | 2 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectiveFoundation.lean`
- module: `InfoGeometry.Canonical.ProjectiveFoundation`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L51 [soft] `law-field-locker` in `structure-field ProjectiveRotorCocycle.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field ProjectiveRotorCocycle.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field ProjectiveRotorCocycle.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ProjectiveRotorCocycle.coe` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `skeletal-proof` in `theorem baseAction_is_genuine` — proof appears to close via minimal tactic one-liner
  - L99 [advisory] `local-hypothesis-injection` in `def extractStabilizerHom` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L137 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.op` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L138 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.KreinPreserving` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L139 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.op_preserves` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L140 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.op_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L141 [soft] `law-field-locker` in `structure-field KreinProjectiveCarrier.op_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

