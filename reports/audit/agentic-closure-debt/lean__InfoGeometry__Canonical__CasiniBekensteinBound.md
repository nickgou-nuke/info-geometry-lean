# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:49.060295+00:00`
Root: `lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/CasiniBekensteinBound.lean`
- module: `InfoGeometry.Canonical.CasiniBekensteinBound`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field State.is_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `class-field CasiniBekensteinContext.relative_entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `class-field CasiniBekensteinContext.relative_entropy_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `class-field CasiniBekensteinContext.entropy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `class-field CasiniBekensteinContext.ModularHamiltonian` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `class-field CasiniBekensteinContext.casini_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field BekensteinGeometricBridge.h_K` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `skeletal-proof` in `theorem true_bekenstein_bound` — proof appears to close via minimal tactic one-liner
  - L92 [advisory] `local-hypothesis-injection` in `theorem true_bekenstein_bound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `local-hypothesis-injection` in `theorem true_bekenstein_bound` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

